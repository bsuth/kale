local C = {}

-- -----------------------------------------------------------------------------
-- Keywords / Terminals
-- -----------------------------------------------------------------------------

C.KEYWORDS = {
  'local',
  'global',
  'module',
  'main',
  'if',
  'elseif',
  'else',
  'for',
  'in',
  'while',
  'repeat',
  'until',
  'do',
  'function',
  'false',
  'true',
  'nil',
  'return',
  'try',
  'catch',
  'break',
  'continue',
}

C.TERMINALS = {
  'true',
  'false',
  'nil',
  '...',
}

-- -----------------------------------------------------------------------------
-- Unops / Binops
-- -----------------------------------------------------------------------------

C.LEFT_ASSOCIATIVE = -1
C.RIGHT_ASSOCIATIVE = 1

C.OP_BLACKLIST = {
  '--', -- Do not parse comments as substraction!
}

C.UNOPS = {
  ['-'] = { prec = 13 },
  ['#'] = { prec = 13 },
  ['!'] = { prec = 13 },
  ['~'] = { prec = 13 },
}

for opToken, op in pairs(C.UNOPS) do
  op.token = opToken
end

C.BINOPS = {
  ['?'] = { prec = 1, assoc = C.LEFT_ASSOCIATIVE },
  ['??'] = { prec = 2, assoc = C.LEFT_ASSOCIATIVE },
  ['||'] = { prec = 3, assoc = C.LEFT_ASSOCIATIVE },
  ['&&'] = { prec = 4, assoc = C.LEFT_ASSOCIATIVE },
  ['=='] = { prec = 5, assoc = C.LEFT_ASSOCIATIVE },
  ['!='] = { prec = 5, assoc = C.LEFT_ASSOCIATIVE },
  ['<='] = { prec = 5, assoc = C.LEFT_ASSOCIATIVE },
  ['>='] = { prec = 5, assoc = C.LEFT_ASSOCIATIVE },
  ['<'] = { prec = 5, assoc = C.LEFT_ASSOCIATIVE },
  ['>'] = { prec = 5, assoc = C.LEFT_ASSOCIATIVE },
  ['|'] = { prec = 6, assoc = C.LEFT_ASSOCIATIVE },
  ['~'] = { prec = 7, assoc = C.LEFT_ASSOCIATIVE },
  ['&'] = { prec = 8, assoc = C.LEFT_ASSOCIATIVE },
  ['<<'] = { prec = 9, assoc = C.LEFT_ASSOCIATIVE },
  ['>>'] = { prec = 9, assoc = C.LEFT_ASSOCIATIVE },
  ['..'] = { prec = 10, assoc = C.LEFT_ASSOCIATIVE },
  ['+'] = { prec = 11, assoc = C.LEFT_ASSOCIATIVE },
  ['-'] = { prec = 11, assoc = C.LEFT_ASSOCIATIVE },
  ['*'] = { prec = 12, assoc = C.LEFT_ASSOCIATIVE },
  ['/'] = { prec = 12, assoc = C.LEFT_ASSOCIATIVE },
  ['%'] = { prec = 12, assoc = C.LEFT_ASSOCIATIVE },
  ['^'] = { prec = 14, assoc = C.RIGHT_ASSOCIATIVE },
}

for opToken, op in pairs(C.BINOPS) do
  op.token = opToken
end

-- These operators cannot be used w/ operator assignment
C.BINOP_ASSIGNMENT_BLACKLIST = {
  ['?'] = true,
  ['=='] = true,
  ['~='] = true,
  ['<='] = true,
  ['>='] = true,
  ['<'] = true,
  ['>'] = true,
}

-- -----------------------------------------------------------------------------
-- Lookup Tables
-- -----------------------------------------------------------------------------

C.SYMBOLS = {
  ['->'] = true,
  ['=>'] = true,
  ['...'] = true,
}

for opToken, op in pairs(C.BINOPS) do
  if #opToken > 1 then
    C.SYMBOLS[opToken] = true
  end
end

-- -----------------------------------------------------------------------------
-- Lookup Tables
-- -----------------------------------------------------------------------------

C.UPPERCASE = {}
C.ALPHA = {}
C.WORD_HEAD = { ['_'] = true }
C.WORD_BODY = { ['_'] = true }
C.DIGIT = {}
C.ALNUM = {}
C.HEX = {}
C.WHITESPACE = {
  ['\n'] = true,
  ['\t'] = true,
  [' '] = true,
}

for byte = string.byte('0'), string.byte('9') do
  local char = string.char(byte)
  C.DIGIT[char] = true
  C.ALNUM[char] = true
  C.HEX[char] = true
  C.WORD_BODY[char] = true
end
for byte = string.byte('A'), string.byte('F') do
  local char = string.char(byte)
  C.ALPHA[char] = true
  C.ALNUM[char] = true
  C.HEX[char] = true
  C.UPPERCASE[char] = true
  C.WORD_HEAD[char] = true
  C.WORD_BODY[char] = true
end
for byte = string.byte('G'), string.byte('Z') do
  local char = string.char(byte)
  C.ALPHA[char] = true
  C.ALNUM[char] = true
  C.UPPERCASE[char] = true
  C.WORD_HEAD[char] = true
  C.WORD_BODY[char] = true
end
for byte = string.byte('a'), string.byte('f') do
  local char = string.char(byte)
  C.ALPHA[char] = true
  C.ALNUM[char] = true
  C.HEX[char] = true
  C.WORD_HEAD[char] = true
  C.WORD_BODY[char] = true
end
for byte = string.byte('g'), string.byte('z') do
  local char = string.char(byte)
  C.ALPHA[char] = true
  C.ALNUM[char] = true
  C.WORD_HEAD[char] = true
  C.WORD_BODY[char] = true
end

-- -----------------------------------------------------------------------------
-- Misc
-- -----------------------------------------------------------------------------

C.EOF = -1

-- -----------------------------------------------------------------------------
-- Return
-- -----------------------------------------------------------------------------

return C
