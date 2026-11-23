#!/data/data/com.termux/files/usr/bin/lua5.5
-- fs: plan/execute filesystem operations with journal + undo
local argparse = require "argparse"
local serpent = require "serpent"
local lpeg = require "lpeg"
local lfs = require "lfs"

local HOME = os.getenv("HOME")
local FSROOT = os.getenv("FSROOT") or (HOME .. "/.local/share/luafs")

local SELF_PID = 0
do
  local f = io.open("/proc/self/stat", "r")
  if f then SELF_PID = tonumber((f:read("*l") or ""):match("^(%d+)")) or 0; f:close() end
end
local PLANDIR = FSROOT .. "/plans"
local TRASH = FSROOT .. "/trash"
for _, d in ipairs({ PLANDIR, TRASH }) do
  if not lfs.attributes(d) then
    local acc = ""
    for part in d:gmatch("[^/]+") do
      acc = acc .. "/" .. part
      if not lfs.attributes(acc) then lfs.mkdir(acc) end
    end
  end
end

-- ---------- path helpers ----------
local function exists(p) return lfs.attributes(p) ~= nil end
local function islink(p) return lfs.symlinkattributes(p, "mode") == "link" end
-- this lfs build has no chmod; shell out (single-quote the path)
local function shq(s) return "'" .. s:gsub("'", "'\\''") .. "'" end
local function chmod(path, mode)
  local ok = os.execute(("chmod %s -- %s"):format(mode, shq(path)))
  if not ok then error("chmod " .. path .. " failed", 0) end
end
local function isdir(p)
  local a = lfs.attributes(p)
  return a and a.mode == "directory"
end
local function abspath(p)
  if p:sub(1, 1) == "~" then p = HOME .. p:sub(2) end
  if p:sub(1, 1) ~= "/" then p = lfs.currentdir() .. "/" .. p end
  local out = {}
  for part in p:gmatch("[^/]+") do
    if part == ".." then table.remove(out)
    elseif part ~= "." then out[#out + 1] = part end
  end
  return "/" .. table.concat(out, "/")
end
local function basename(p) return p:match("([^/]+)$") or "/" end
local function dirname(p) return p:match("^(.*)/[^/]+$") or "/" end

local function mkdirs(path)
  local created, acc = {}, ""
  for part in path:gmatch("[^/]+") do
    acc = acc .. "/" .. part
    if not exists(acc) then
      lfs.mkdir(acc)
      created[#created + 1] = acc
    end
  end
  return created
end

local function trash(p)
  local base = basename(p):gsub("/", "_")
  local n, dst = 0, nil
  repeat
    n = n + 1
    dst = ("%s/%d-%d-%d-%s"):format(TRASH, os.time(), SELF_PID, n, base)
  until not exists(dst)
  assert(os.rename(p, dst), "trash failed for " .. p)
  return dst
end

local function restore(trashfile, orig)
  if trashfile and exists(trashfile) then
    mkdirs(dirname(orig))
    assert(os.rename(trashfile, orig), "restore failed for " .. orig)
  end
end

local function octal_from_perms(s)
  -- "rwxr-xr-x" -> "755"
  local function triad(t)
    return (t:sub(1, 1) == "r" and 4 or 0) + (t:sub(2, 2) == "w" and 2 or 0)
      + (t:sub(3, 3) == "x" and 1 or 0)
  end
  return ("%d%d%d"):format(triad(s:sub(1, 3)), triad(s:sub(4, 6)), triad(s:sub(7, 9)))
end

local function filecopy(src, dst)
  local i, o = assert(io.open(src, "rb")), assert(io.open(dst, "wb"))
  while true do
    local chunk = i:read(1 << 20)
    if not chunk then break end
    assert(o:write(chunk))
  end
  o:close()
  i:close()
  chmod(dst, octal_from_perms(lfs.attributes(src, "permissions")))
end

local function rrmdir(p)
  for f in lfs.dir(p) do
    if f ~= "." and f ~= ".." then
      local fp = p .. "/" .. f
      if isdir(fp) and not islink(fp) then rrmdir(fp)
      else assert(os.remove(fp), "cannot remove " .. fp) end
    end
  end
  assert(lfs.rmdir(p))
end

local function walk(p, out)
  out[#out + 1] = p
  if isdir(p) then
    for f in lfs.dir(p) do
      if f ~= "." and f ~= ".." then walk(p .. "/" .. f, out) end
    end
  end
  return out
end

-- ---------- safety guard for rm ----------
local function guard(p)
  local allowed = p ~= HOME and p:sub(1, #HOME + 1) == HOME .. "/"
    or p:sub(1, 5) == "/tmp/"
    or p:sub(1, #FSROOT + 1) == FSROOT .. "/"
  if not allowed then
    error("refusing operation on '" .. p .. "'", 0)
  end
end

-- ---------- chmod expression parsing (lpeg) ----------
local function parse_mode(expr, old)
  if expr:match("^%d+$") then return tonumber(expr, 8) end
  local perms = { r = 4, w = 2, x = 1, X = 1 } -- lpeg turns this language trivial, keeping table parse for value math
  local grammar = lpeg.Ct(lpeg.Ct(
      lpeg.C(lpeg.S("ugoa") ^ 0) * lpeg.C(lpeg.S("+-=")) * lpeg.C(lpeg.S("rwxX") ^ 1)
    ) ^ 1)
  local clauses = grammar:match(expr)
  assert(clauses, "bad chmod expr: " .. tostring(expr))
  local bits = {}
  for i, t in ipairs({ old:sub(1, 3), old:sub(4, 6), old:sub(7, 9) }) do
    local b = (t:sub(1, 1) == "r" and 4 or 0) + (t:sub(2, 2) == "w" and 2 or 0)
      + (t:sub(3, 3) == "x" and 1 or 0)
    bits[i] = b
  end
  local whoidx = { u = 1, g = 2, o = 3 }
  for _, cl in ipairs(clauses) do
    local who, op, pl = cl[1], cl[2], cl[3]
    local mask = 0
    for c in pl:gmatch(".") do mask = mask + (perms[c] or 0) end
    local targets = {}
    if who == "" or who:find("a", 1, true) then
      targets = { 1, 2, 3 }
    else
      for c in who:gmatch(".") do
        local n = whoidx[c]
        if n then targets[#targets + 1] = n end
      end
    end
    for _, i in ipairs(targets) do
      if op == "+" then bits[i] = bits[i] | mask
      elseif op == "-" then bits[i] = bits[i] & ~mask
      else bits[i] = mask end
    end
  end
  return (bits[1] << 6) | (bits[2] << 3) | bits[3]
end

-- ---------- step runners: run fills st.done, undo reverts ----------
local STEPS = {}

STEPS.mkdir = {
  run = function(st)
    if exists(st.path) then error(st.path .. " exists", 0) end
    st.done = { created = mkdirs(st.path) }
    if st.expr then
      for _, c in ipairs(st.done.created) do
        chmod(c, st.expr)
      end
    end
  end,
  undo = function(st)
    local c = st.done.created
    for i = #c, 1, -1 do pcall(lfs.rmdir, c[i]) end
  end,
}

STEPS.filecopy = {
  run = function(st)
    st.done = {}
    if isdir(st.src) then error("filecopy on directory " .. st.src, 0) end
    mkdirs(dirname(st.dst))
    local tmp = st.dst .. ".fs-tmp-" .. SELF_PID
    filecopy(st.src, tmp)
    if exists(st.dst) then st.done.replaced = trash(st.dst) end
    assert(os.rename(tmp, st.dst), "rename failed for " .. st.dst)
  end,
  undo = function(st)
    if exists(st.dst) then trash(st.dst) end
    restore(st.done.replaced, st.dst)
  end,
}

STEPS.move = {
  run = function(st)
    local ok, err = os.rename(st.src, st.dst)
    if not ok then
      error("move failed: " .. tostring(err) .. " (cross-device unsupported)", 0)
    end
    st.done = { src = st.src, dst = st.dst }
  end,
  undo = function(st)
    os.rename(st.done.dst, st.done.src)
  end,
}

STEPS.trash = {
  run = function(st) st.done = { file = trash(st.path) } end,
  undo = function(st) restore(st.done.file, st.path) end,
}

STEPS.chmod = {
  run = function(st)
    local old = lfs.attributes(st.path, "permissions")
    local n = parse_mode(st.expr, old)
    chmod(st.path, ("%o"):format(n))
    st.done = { old = octal_from_perms(old) }
  end,
  undo = function(st) chmod(st.path, st.done.old) end,
}

-- ---------- planner ----------
local function resolve_target(src, dst, force)
  if isdir(dst) then dst = dst .. "/" .. basename(src) end
  if exists(dst) then
    if isdir(dst) then error("cannot overwrite directory " .. dst, 0) end
    if not force then error(dst .. " exists (use --force)", 0) end
  end
  if dst == src then error("src and dst are the same", 0) end
  return dst
end

local planner = {}

function planner.cp(srcs, dst, force)
  dst = abspath(dst)
  if #srcs > 1 and not isdir(dst) then
    error("multiple sources require an existing destination directory", 0)
  end
  local plan = {}
  for _, src in ipairs(srcs) do
    src = abspath(src)
    if not exists(src) then error(src .. ": not found", 0) end
    local tgt = resolve_target(src, dst, force)
    local function flatten(s, d)
      plan[#plan + 1] = { op = "mkdir", path = d }
      plan[#plan + 1] = { op = "chmod", path = d, expr = octal_from_perms(lfs.attributes(s, "permissions")) }
      for f in lfs.dir(s) do
        if f ~= "." and f ~= ".." then
          local ss, dd = s .. "/" .. f, d .. "/" .. f
          if isdir(ss) and not islink(ss) then flatten(ss, dd)
          else plan[#plan + 1] = { op = "filecopy", src = ss, dst = dd } end
        end
      end
    end
    if isdir(src) then flatten(src, tgt)
    else plan[#plan + 1] = { op = "filecopy", src = src, dst = tgt } end
  end
  return plan
end

function planner.mv(srcs, dst, force)
  dst = abspath(dst)
  if #srcs > 1 and not isdir(dst) then
    error("multiple sources require an existing destination directory", 0)
  end
  local plan = {}
  for _, src in ipairs(srcs) do
    src = abspath(src)
    if not exists(src) then error(src .. ": not found", 0) end
    local tgt = resolve_target(src, dst, force)
    if isdir(src) ~= isdir(dst) and exists(tgt) then
      error("mv dir onto " .. tgt .. " not supported", 0)
    end
    plan[#plan + 1] = { op = "move", src = src, dst = tgt }
  end
  return plan
end

function planner.mkdir(dirs, mode)
  if mode then
    if not mode:match("^[0-7]+$") then error("mode must be octal: " .. mode, 0) end
    mode = ("%o"):format(tonumber(mode, 8))
  end
  local plan = {}
  for _, d in ipairs(dirs) do
    d = abspath(d)
    if exists(d) then error(d .. " already exists", 0) end
    plan[#plan + 1] = { op = "mkdir", path = d, expr = mode }
  end
  return plan
end

function planner.rm(paths)
  local plan = {}
  for _, p in ipairs(paths) do
    p = abspath(p)
    guard(p)
    if not exists(p) then error(p .. ": not found", 0) end
    local all = walk(p, {})
    for i = #all, 1, -1 do -- children before parent
      plan[#plan + 1] = { op = "trash", path = all[i] }
    end
  end
  return plan
end

function planner.chmod(expr, paths, recursive)
  local plan = {}
  for _, p in ipairs(paths) do
    p = abspath(p)
    if not exists(p) then error(p .. ": not found", 0) end
    local targets = recursive and walk(p, {}) or { p }
    for _, t in ipairs(targets) do
      plan[#plan + 1] = { op = "chmod", path = t, expr = expr }
    end
  end
  return plan
end

-- ---------- executor + journal ----------
local function last_seq()
  local max = 0
  for f in lfs.dir(PLANDIR) do
    local n = tonumber(f:match("^(%d+)%.serpent$"))
    if n and n > max then max = n end
  end
  return max
end

local function jload(s)
  local chunk = assert(load("return " .. s, "journal", "t", {}))
  return chunk()
end

-- journal file: line 1 is the plan; each next line is the done data of one
-- completed step, appended and flushed right after that step runs.
-- shortcut: a hard kill inside a step can leave that one step's partial work
-- unrecorded; completed steps are still undoable.
local function execute(plan)
  local seq = last_seq() + 1
  local path = ("%s/%d.serpent"):format(PLANDIR, seq)
  local jf = assert(io.open(path, "w"))
  jf:write(serpent.line(plan, { comment = false }), "\n")
  jf:close()
  jf = assert(io.open(path, "a"))
  local done, err = 0, nil
  for i, st in ipairs(plan) do
    local r = assert(STEPS[st.op], "no runner for " .. tostring(st.op))
    local ok, e = pcall(r.run, st)
    if not ok then
      err = ("step %d failed: %s"):format(i, tostring(e))
      local half = not pcall(r.undo, st)
      jf:close()
      local left = half and 1 or 0
      for j = done, 1, -1 do
        if not pcall(STEPS[plan[j].op].undo, plan[j]) then left = left + 1 end
      end
      if left == 0 then os.remove(path) end
      error(tostring(err):gsub("^.-:%d+: ", ""), 0)
    end
    jf:write(serpent.line(st.done, { comment = false }), "\n")
    jf:flush()
    done = i
  end
  jf:close()
  return seq
end

local function undo()
  local seq = last_seq()
  if seq < 1 then error("nothing to undo", 0) end
  local path = ("%s/%d.serpent"):format(PLANDIR, seq)
  local f = assert(io.open(path, "r"))
  local plan = jload(f:read("*l") or "")
  local recs = {}
  for line in f:lines() do recs[#recs + 1] = jload(line) end
  f:close()
  local n = math.min(#recs, #plan)
  for i = 1, n do plan[i].done = recs[i] end
  local left = 0
  for i = n, 1, -1 do
    local st = plan[i]
    local r = STEPS[st.op]
    if not r or not pcall(r.undo, st) then
      io.stderr:write(("fs: undo step %d failed\n"):format(i))
      left = left + 1
    end
  end
  os.rename(path, path .. ".undone")
  if left > 0 then
    error(("%d undo step(s) failed (journal marked undone)"):format(left), 0)
  end
end

-- ---------- CLI (argparse, one parser per verb) ----------
local function main()
local cmd = table.remove(arg, 1)
if not cmd then
  io.stderr:write("usage: fs <cp|mv|mkdir|rm|chmod|undo|plans> [--dry-run]\n")
  os.exit(2)
end

if cmd == "undo" then return undo() end
if cmd == "plans" then
  for f in lfs.dir(PLANDIR) do print(f) end
  return
end

local ap = argparse("fs " .. cmd)
local dry = false
for i = #arg, 1, -1 do
  if arg[i] == "--dry-run" then dry = true; table.remove(arg, i) end
end
local plan, parsed

if cmd == "cp" then
  ap:flag("-f --force", "overwrite existing files")
  ap:argument("sources"):args("+")
  local dest
  for i = #arg, 1, -1 do
    if arg[i]:sub(1, 1) ~= "-" then dest = table.remove(arg, i); break end
  end
  parsed = ap:parse(arg)
  plan = planner.cp(parsed.sources, dest, parsed.force)
elseif cmd == "mv" then
  ap:flag("-f --force", "overwrite existing files")
  ap:argument("sources"):args("+")
  local dest
  for i = #arg, 1, -1 do
    if arg[i]:sub(1, 1) ~= "-" then dest = table.remove(arg, i); break end
  end
  parsed = ap:parse(arg)
  plan = planner.mv(parsed.sources, dest, parsed.force)
elseif cmd == "mkdir" then
  ap:option("-m --mode", "permissions as octal"):args(1)
  ap:argument("dirs"):args("+")
  parsed = ap:parse(arg)
  plan = planner.mkdir(parsed.dirs, parsed.mode)elseif cmd == "rm" then
  ap:argument("paths"):args("+")
  parsed = ap:parse(arg)
  plan = planner.rm(parsed.paths) -- minimal: no interactivity; all targets go to trash
elseif cmd == "chmod" then
  ap:flag("-R --recursive", "recurse into directories")
  ap:argument("mode")
  ap:argument("paths"):args("+")
  parsed = ap:parse(arg)
  plan = planner.chmod(parsed.mode, parsed.paths, parsed.recursive)
else
  io.stderr:write("unknown command " .. cmd .. "\n")
  os.exit(2)
end

local function show(p)
  for i, st in ipairs(p) do
    local line = {
      mkdir = ("%2d mkdir  %s"):format(i, st.path),
      filecopy = ("%2d copy   %s -> %s"):format(i, st.src, st.dst),
      move = ("%2d move   %s -> %s"):format(i, st.src, st.dst),
      trash = ("%2d trash  %s"):format(i, st.path),
      chmod = ("%2d chmod  %s %s"):format(i, st.expr, st.path),
    }
    print(line[st.op])
  end
end

if dry then
  show(plan)
else
  local seq = execute(plan)
  io.stderr:write(("plan %d executed (%d steps)\n"):format(seq, #plan))
end
end

local ok, err = pcall(main)
if not ok then
  io.stderr:write(tostring(err):gsub("^.-:%d+: ", ""), "\n")
  os.exit(1)
end
