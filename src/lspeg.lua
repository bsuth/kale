local lpeg = require('lpeg')

lpeg.locale(lpeg)
local P = lpeg.P
local C, Cc, Cg, Cp, Ct = lpeg.C, lpeg.Cc, lpeg.Cg, lpeg.Cp, lpeg.Ct
local space = lpeg.space

-- -----------------------------------------------------------------------------
-- Module
-- -----------------------------------------------------------------------------

local lspeg = {}

-- -----------------------------------------------------------------------------
-- Extended Pattern Helpers
-- -----------------------------------------------------------------------------

--
-- Exact
--

function lspeg.E(pattern, n)
  return (pattern ^ n) ^ -n
end

--
-- Word
--

function lspeg.W(pattern)
  return (space ^ 0) * pattern * (space ^ 0)
end

--
-- Word Capture
--

function lspeg.Wc(pattern)
  return (space ^ 0) * C(pattern) * (space ^ 0)
end

-- -----------------------------------------------------------------------------
-- Lists
-- -----------------------------------------------------------------------------

--
-- List
--

function lspeg.L(pattern, separator)
  separator = separator or lspeg.W(',')
  return pattern * (separator * pattern) ^ 0
end

--
-- List Join
--

function lspeg.Lj(patterns, separator)
  separator = separator or lspeg.W(',')

  if #patterns == 0 then
    return P(true)
  end

  local joined = patterns[1]
  for i = 2, #patterns do
    joined = joined * separator * patterns[i]
  end
  return joined
end

-- -----------------------------------------------------------------------------
-- Macros
-- -----------------------------------------------------------------------------

--
-- Macro
--

function lspeg.M(patterns, macro, value)
  local result = value or P(false)

  for i, pattern in ipairs(patterns) do
    result = macro(pattern, value)
  end

  return result
end

--
-- Macro Sum
--

function lspeg.Ms(patterns)
  return lspeg.M(patterns, function(pattern, sum)
    return sum + pattern
  end, P(false))
end

-- -----------------------------------------------------------------------------
-- Tags
-- -----------------------------------------------------------------------------

--
-- Tag
--

function lspeg.T(tag, pattern)
  return Ct(Cg(Cp(), 'position') * Cg(Cc(tag), 'tag') * pattern)
end

-- -----------------------------------------------------------------------------
-- Return
-- -----------------------------------------------------------------------------

return lspeg
