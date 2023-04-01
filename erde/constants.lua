local C = {}

C.VERSION = '0.5-1'

-- Get the current platform path separator. Note that while this is undocumented
-- in the Lua 5.1 manual, it is indeed supported in 5.1+.
--
-- https://www.lua.org/manual/5.3/manual.html#pdf-package.config
C.PATH_SEPARATOR = package.config:sub(1, 1)

-- A footer comment we inject into compiled code in order to track which files
-- have been generated by the cli (and thus allows us to also clean them later).
C.COMPILED_FOOTER_COMMENT = '-- __ERDE_COMPILED__'

-- Flag to know whether or not we are running under the cli. Required for more
-- precise error rewriting.
C.IS_CLI_RUNTIME = false

  -- User specified library to use for bit operations.
C.BITLIB = nil

-- -----------------------------------------------------------------------------
-- Lua Target
-- -----------------------------------------------------------------------------

C.LUA_TARGET = '5.1+'

C.VALID_LUA_TARGETS = {
  'jit',
  '5.1',
  '5.1+',
  '5.2',
  '5.2+',
  '5.3',
  '5.3+',
  '5.4',
  '5.4+',
}

for i, target in ipairs(C.VALID_LUA_TARGETS) do
  C.VALID_LUA_TARGETS[target] = true
end

-- -----------------------------------------------------------------------------
-- Return
-- -----------------------------------------------------------------------------

return C
