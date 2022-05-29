local C = require('erde.constants')
local tokenize = require('erde.tokenize')

-- Foward declare rules
local Block, Destructure, Expr, OptChain

-- -----------------------------------------------------------------------------
-- State
-- -----------------------------------------------------------------------------

local tokens, tokenInfo, newlines
local currentTokenIndex, currentToken

-- -----------------------------------------------------------------------------
-- Helpers
-- -----------------------------------------------------------------------------

local function consume()
  local consumedToken = tokens[currentTokenIndex]
  currentTokenIndex = currentTokenIndex + 1
  currentToken = tokens[currentTokenIndex]
  return consumedToken
end

local function lookBehind(n)
  return tokens[currentTokenIndex - n] or ''
end

local function lookAhead(n)
  return tokens[currentTokenIndex + n] or ''
end

local function branch(token)
  if token == currentToken then
    consume()
    return true
  end
end

local function expect(token)
  if token ~= currentToken then
    error('Expected ' .. token .. ' got ' .. tostring(currentToken))
  end
  consume()
end

-- -----------------------------------------------------------------------------
-- Macros
-- -----------------------------------------------------------------------------

local function Try(rule)
  local currentTokenIndexBackup = currentTokenIndex
  local ok, node = pcall(rule)

  if ok then
    return node
  else
    currentTokenIndex = currentTokenIndexBackup
    currentToken = tokens[currentTokenIndex]
  end
end

local function Surround(openChar, closeChar, parse)
  expect(openChar)
  local node = parse()
  expect(closeChar)
  return node
end

local function Parens(opts)
  if currentToken ~= '(' and not opts.demand then
    return opts.parse()
  else
    opts.demand = false

    if opts.prioritizeRule then
      local node = Try(opts.parse)
      if node then
        return node
      end
    end

    return Surround('(', ')', function()
      return opts.allowRecursion and Parens(opts) or opts.parse()
    end)
  end
end

local function List(opts)
  local list = {}
  local hasTrailingComma = false

  repeat
    local node = Try(opts.parse)
    if not node then
      break
    end

    hasTrailingComma = branch(',')
    table.insert(list, node)
  until not hasTrailingComma

  assert(opts.allowTrailingComma or not hasTrailingComma)
  assert(opts.allowEmpty or #list > 0)

  return list
end

-- -----------------------------------------------------------------------------
-- Pseudo Rules
-- -----------------------------------------------------------------------------

local function Name(opts)
  assert(
    currentToken:match('^[_a-zA-Z][_a-zA-Z0-9]*$'),
    'Malformed name: ' .. currentToken
  )

  if not opts or not opts.allowKeywords then
    for i, keyword in pairs(C.KEYWORDS) do
      assert(currentToken ~= keyword, 'Unexpected keyword: ' .. currentToken)
    end
  end

  return consume()
end

local function Var()
  return (currentToken == '{' or currentToken == '[') and Destructure()
    or Name()
end

local function Id()
  local node = OptChain()
  local last = node[#node]

  if last and last.variant == 'functionCall' then
    error('Unexpected function call')
  end

  return node
end

local function Spread()
  expect('...')
  return { tag = 'Spread', value = Try(Expr) }
end

-- -----------------------------------------------------------------------------
-- Destructure
-- -----------------------------------------------------------------------------

local function ArrayDestructure()
  return Surround('[', ']', function()
    return List({
      allowTrailingComma = true,
      parse = function()
        return {
          name = Name(),
          variant = 'numberDestruct',
          default = branch('=') and Expr(),
        }
      end,
    })
  end)
end

local function MapDestructure()
  return Surround('{', '}', function()
    return List({
      allowTrailingComma = true,
      parse = function()
        return {
          name = Name(),
          variant = 'keyDestruct',
          alias = branch(':') and Name(),
          default = branch('=') and Expr(),
        }
      end,
    })
  end)
end

function Destructure()
  local node = currentToken == '[' and ArrayDestructure()
    or MapDestructure()
  node.tag = 'Destructure'
  return node
end

-- -----------------------------------------------------------------------------
-- Params
-- -----------------------------------------------------------------------------

local function ParamsList()
  local paramsList = List({
    allowEmpty = true,
    allowTrailingComma = true,
    parse = function()
      return {
        value = Var(),
        default = branch('=') and Expr(),
      }
    end,
  })

  if (#paramsList == 0 or lookBehind(1) == ',') and branch('...') then
    table.insert(paramsList, {
      value = Try(Name),
      varargs = true,
    })
  end

  return paramsList
end

local function Params(allowImplicitParams)
  local node
  if currentToken ~= '(' and allowImplicitParams then
    node = { { value = Var() } }
  else
    node = Parens({ demand = true, parse = ParamsList })
  end

  node.tag = 'Params'
  return node
end

-- -----------------------------------------------------------------------------
-- OptChain
-- -----------------------------------------------------------------------------

local function OptChainBase()
  if currentToken == '(' then
    local base = Surround('(', ')', Expr)

    if type(base) == 'table' then
      base.parens = true
    end

    return base
  else
    return Name()
  end
end

local function OptChainDotIndex()
  local name = Try(function()
    return Name({ allowKeywords = true })
  end)

  return name and { variant = 'dotIndex', value = name }
end

local function OptChainMethod()
  local name = Try(function()
    return Name({ allowKeywords = true })
  end)

  local isNextChainFunctionCall = currentToken == '('
    or (currentToken == '?' and lookAhead(1) == '(')

  if name and isNextChainFunctionCall then
    return { variant = 'method', value = name }
  else
    error('Missing parentheses for method call')
  end
end

local function OptChainBracket()
  return {
    variant = 'bracketIndex',
    value = Surround('[', ']', Expr),
  }
end

local function OptChainFunctionCall()
  return {
    variant = 'functionCall',
    value = Parens({
      demand = true,
      parse = function()
        return List({
          allowEmpty = true,
          allowTrailingComma = true,
          parse = function()
            return currentToken == '...' and Spread() or Expr()
          end,
        })
      end,
    }),
  }
end

function OptChain()
  local node = {
    tag = 'OptChain',
    base = OptChainBase(),
  }

  while true do
    local currentTokenIndexBackup = currentTokenIndex
    local isOptional = branch('?')

    local chain
    if branch('.') then
      chain = OptChainDotIndex()
    elseif branch(':') then
      chain = OptChainMethod()
    elseif currentToken == '[' then
      chain = OptChainBracket()
    elseif currentToken == '(' then
      if not newlines[currentTokenIndex - 1] then
        chain = OptChainFunctionCall()
      end
    end

    if not chain then
      currentTokenIndex = currentTokenIndexBackup
      currentToken = tokens[currentTokenIndex]
      break
    end

    chain.optional = isOptional
    table.insert(node, chain)
  end

  return #node == 0 and node.base or node -- unpack trivial OptChain
end

-- -----------------------------------------------------------------------------
-- Expr
-- -----------------------------------------------------------------------------

local function ArrowFunction()
  local node = {
    tag = 'ArrowFunction',
    params = Params(true),
    hasFatArrow = consume() == '=>',
    hasImplicitReturns = false,
  }

  if currentToken == '{' then
    node.body = Surround('{', '}', Block)
  elseif currentToken == '(' then
    node.hasImplicitReturns = true
    node.returns = Parens({
      allowRecursion = true,
      parse = function()
        return List({
          allowTrailingComma = true,
          parse = Expr,
        })
      end,
    })
  else
    node.hasImplicitReturns = true
    node.returns = { Expr() }
  end

  return node
end

local function TableField()
  local field = {}

  if currentToken == '[' then
    field.variant = 'exprKey'
    field.key = Surround('[', ']', Expr)
  elseif currentToken == '...' then
    field.variant = 'spread'
    field.value = Spread()
  else
    local expr = Expr()

    if
      currentToken == '='
      and type(expr) == 'string'
      and expr:match('^[_a-zA-Z][_a-zA-Z0-9]*$')
    then
      field.variant = 'nameKey'
      field.key = expr
    else
      field.variant = 'numberKey'
      field.value = expr
    end
  end

  if field.variant == 'exprKey' or field.variant == 'nameKey' then
    expect('=')
    field.value = Expr()
  end

  return field
end

local function Table()
  local node = Surround('{', '}', function()
    return List({
      allowEmpty = true,
      allowTrailingComma = true,
      parse = TableField,
    })
  end)

  node.tag = 'Table'
  return node
end

local function Terminal()
  for _, terminal in pairs(C.TERMINALS) do
    if branch(terminal) then
      return terminal
    end
  end

  if currentToken:match('^.?[0-9]') then
    -- Only need to check first couple chars, rest is token care of by tokenizer
    return consume()
  elseif branch('do') then
    return { tag = 'DoBlockExpr', body = Surround('{', '}', Block) }
  elseif currentToken == "'" then
    return consume() .. consume() .. consume()
  elseif currentToken == '"' or currentToken:match('^%[[[=]') then
    local node = { tag = 'String' }
    local terminatingToken

    if currentToken == '"' then
      node.variant = 'double'
      terminatingToken = consume()
    else
      node.variant = 'long'
      node.equals = ('='):rep(#currentToken - 2)
      terminatingToken = ']' .. node.equals .. ']'
      consume()
    end

    while currentToken ~= terminatingToken do
      table.insert(node, currentToken == '{'
        and { variant = 'interpolation', value = Surround('{', '}', Expr) }
        or { variant = 'content', value = consume() }
      )
    end

    consume() -- terminatingToken
    return node
  end

  local nextToken = lookAhead(1)
  local isArrowFunction = nextToken == '->' or nextToken == '=>' or currentToken == '['
  local surroundEnd = currentToken == '(' and ')'
    or currentToken == '{' and '}'
    or nil

  if not isArrowFunction and surroundEnd then
    local surroundStart = currentToken
    local surroundDepth = 0

    local tokenIndex = currentTokenIndex + 1
    local token = tokens[tokenIndex]

    while token ~= surroundEnd or surroundDepth > 0 do
      if token == nil then
        error('Unexpected EOF')
      elseif token == surroundStart then
        surroundDepth = surroundDepth + 1
      elseif token == surroundEnd then
        surroundDepth = surroundDepth - 1
      end

      tokenIndex = tokenIndex + 1
      token = tokens[tokenIndex]
    end

    -- Check one past surrounds for arrow
    tokenIndex = tokenIndex + 1
    token = tokens[tokenIndex]
    isArrowFunction = token == '->' or token == '=>'
  end

  if isArrowFunction then
    return ArrowFunction()
  elseif currentToken == '{' then
    return Table()
  else
    return OptChain()
  end
end

function Expr(minPrec)
  minPrec = minPrec or 1

  local node
  if C.UNOPS[currentToken] then
    local unop = C.UNOPS[consume()]
    node = { tag = 'Unop', op = unop, operand = Expr(unop.prec + 1) }
  else
    node = Terminal()
  end

  local binop = C.BINOPS[currentToken]
  while binop and binop.prec >= minPrec do
    consume()

    local rhsPrec = binop.prec
    if binop.assoc == C.LEFT_ASSOCIATIVE then
      rhsPrec = rhsPrec + 1
    end

    node = { tag = 'Binop', op = binop, lhs = node, rhs = Expr(rhsPrec) }
    binop = C.BINOPS[currentToken]
  end

  return node
end

-- -----------------------------------------------------------------------------
-- Block
-- -----------------------------------------------------------------------------

function Block()
  local node = { tag = 'Block' }

  repeat
    local statement

    if branch('break') then
      statement = { tag = 'Break' }
    elseif branch('continue') then
      statement = { tag = 'Continue' }
    elseif branch('do') then
      statement = { tag = 'DoBlockStatement', body = Surround('{', '}', Block) }
    elseif branch('goto') then
      statement = { tag = 'Goto', name = Name() }
    elseif branch('::') then
      statement = { tag = 'GotoLabel', name = Name() }
      expect('::')
    elseif branch('while') then
      statement = { tag = 'WhileLoop', condition = Expr(), body = Surround('{', '}', Block) }
    elseif branch('repeat') then
      statement = { tag = 'RepeatUntil', body = Surround('{', '}', Block) }
      expect('until')
      statement.condition = Expr()
    elseif branch('try') then
      statement = { tag = 'TryCatch', try = Surround('{', '}', Block) }
      expect('catch')
      statement.error = Try(Var)
      statement.catch = Surround('{', '}', Block)
    elseif branch('return') then
      statement = currentToken ~= '('
        and List({ parse = Expr, allowEmpty = true })
        or Parens({
          allowRecursion = true,
          prioritizeRule = true,
          parse = function()
            return List({
              allowTrailingComma = true,
              parse = Expr,
            })
          end,
        })
      statement.tag = 'Return'
    elseif branch('if') then
      statement = {
        tag = 'IfElse',
        ifNode = { condition = Expr(), body = Surround('{', '}', Block) }
      }

      local elseifNodes = {}
      while branch('elseif') do
        table.insert(elseifNodes, {
          condition = Expr(),
          body = Surround('{', '}', Block),
        })
      end
      statement.elseifNodes = elseifNodes

      if branch('else') then
        statement.elseNode = { body = Surround('{', '}', Block) }
      end
    elseif branch('for') then
      local firstName = Var()

      if type(firstName) == 'string' and branch('=') then
        statement = {
          tag = 'NumericFor',
          name = firstName,
          parts = List({ parse = Expr }),
        }
      else
        statement = { tag = 'GenericFor' }
        local varList = { firstName }

        while branch(',') do
          table.insert(varList, Var())
        end

        statement.varList = varList
        expect('in')
        statement.exprList = List({ parse = Expr })
      end

      statement.body = Surround('{', '}', Block)
    elseif currentToken == 'function' or lookAhead(1) == 'function' then
      statement = { tag = 'Function', isMethod = false }

      if currentToken == 'local' or currentToken == 'global' or currentToken == 'module' then
        statement.variant = consume()
      elseif currentToken ~= 'function' then
        error('Unrecognized scope before function declaration: ' .. currentToken)
      end

      consume() -- 'function'
      local names = { Name() }

      while branch('.') do
        table.insert(names, Name())
      end

      if branch(':') then
        statement.isMethod = true
        table.insert(names, Name())
      end

      if not statement.variant then
        -- Default functions to local scope _unless_ they are part of a table.
        statement.variant = #names > 1 and 'global' or 'local'
      end

      statement.names = names
      statement.params = Params()
      statement.body = Surround('{', '}', Block)
    elseif currentToken == 'local' or currentToken == 'global' or currentToken == 'module' then
      -- This must come after we check for function declaration!
      statement = {
        tag = 'Declaration',
        variant = consume(),
        varList = List({ parse = Var }),
        exprList = branch('=') and List({ parse = Expr }) or {},
      }
    else
      local optChain = Try(OptChain)

      if optChain then
        local optChainLast = optChain[#optChain]

        if optChainLast and optChainLast.variant == 'functionCall' then
          -- Allow function calls as standalone statements
          statement = optChain
        else
          statement = { tag = 'Assignment' }
          statement.idList = branch(',') and List({ parse = Id }) or {}
          table.insert(statement.idList, 1, optChain)

          if C.BINOP_ASSIGNMENT_BLACKLIST[currentToken] then
            error('Invalid assignment operator: ' .. currentToken)
          elseif C.BINOPS[currentToken] then
            statement.op = C.BINOPS[consume()]
          end

          expect('=')
          statement.exprList = List({ parse = Expr })
        end
      end
    end

    table.insert(node, statement)
  until not statement

  return node
end

-- =============================================================================
-- Return
-- =============================================================================

return function(text)
  local ast = {}

  tokens, tokenInfo, newlines = tokenize(text)
  currentTokenIndex = 1
  currentToken = tokens[1]

  -- Check for empty file or file w/ only comments
  if currentToken == nil then
    return nil
  end

  local shebang
  if currentToken:match('^#!') then
    shebang = consume()
  end

  local ast = Block()
  ast.shebang = shebang

  return ast
end
