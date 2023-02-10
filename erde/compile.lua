local C = require('erde.constants')
local utils = require('erde.utils')
local tokenize = require('erde.tokenize')

-- Foward declare
local Expr, Block

-- -----------------------------------------------------------------------------
-- State
-- -----------------------------------------------------------------------------

local tokens, token_lines
local current_token, current_token_index
local current_line

-- Current block depth during parsing
local block_depth = 0

-- Counter for generating unique names in compiled code.
local tmp_name_counter

-- Break name to use for `continue` statements. This is also used to validate
-- the context of `break` and `continue`.
local break_name

-- Flag to keep track of whether the current block has any `continue` statements.
local has_continue

-- Table for Declaration and Function to register `module` scope variables.
local module_names

-- Keeps track of whether the module has a `return` statement. Used to warn the
-- developer if they try to combine `return` with `module` scopes.
local is_module_return_block, has_module_return

-- Keeps track of whether the current block can use varargs as an expression.
-- Required since the Lua _parser_ will throw an error if varargs are used
-- outside a vararg function.
local is_varargs_block

-- Resolved bit library to use for compiling bit operations. Undefined when
-- compiling to Lua 5.3+ native operators.
local bitlib

-- -----------------------------------------------------------------------------
-- General Helpers
-- -----------------------------------------------------------------------------

local unpack = table.unpack or unpack
local insert = table.insert
local concat = table.concat

-- -----------------------------------------------------------------------------
-- Parse Helpers
-- -----------------------------------------------------------------------------

local function consume()
  local consumed_token = current_token
  current_token_index = current_token_index + 1
  current_token = tokens[current_token_index]
  current_line = token_lines[current_token_index]
  return consumed_token
end

local function branch(token)
  if token == current_token then
    consume()
    return true
  end
end

local function ensure(is_valid, message)
  if not is_valid then
    utils.erde_error({
      message = message,
      line = current_line,
    })
  end
end

local function expect(token, prevent_consume)
  ensure(current_token ~= nil, ('unexpected eof (expected %s)'):format(token))
  ensure(token == current_token, ("expected '%s' got '%s'"):format(token, current_token))
  if not prevent_consume then return consume() end
end

local function look_ahead(n)
  return tokens[current_token_index + n]
end

local function look_past_surround(token_start_index)
  token_start_index = token_start_index or current_token_index
  local surround_start = tokens[token_start_index]
  local surround_end = C.SURROUND_ENDS[surround_start]
  local surround_depth = 1

  local look_ahead_token_index = token_start_index + 1
  local look_ahead_token = tokens[look_ahead_token_index]

  while surround_depth > 0 do
    if look_ahead_token == nil then
      utils.erde_error({
        line = token_lines[look_ahead_token_index - 1],
        message = ("unexpected eof, missing ending '%s' for '%s' at [%d]"):format(
          surround_end,
          surround_start,
          token_lines[token_start_index]
        ),
      })
    elseif look_ahead_token == surround_start then
      surround_depth = surround_depth + 1
    elseif look_ahead_token == surround_end then
      surround_depth = surround_depth - 1
    end

    look_ahead_token_index = look_ahead_token_index + 1
    look_ahead_token = tokens[look_ahead_token_index]
  end

  return look_ahead_token, look_ahead_token_index
end

-- -----------------------------------------------------------------------------
-- Compile Helpers
-- -----------------------------------------------------------------------------

local function new_tmp_name()
  tmp_name_counter = tmp_name_counter + 1
  return ('__ERDE_TMP_%d__'):format(tmp_name_counter)
end

local function weave(t, separator)
  separator = separator or ','
  local woven = {}
  local len = #t

  for i = 1, len - 1 do
    insert(woven, t[i])
    if type(t[i]) ~= 'number' then
      insert(woven, separator)
    end
  end

  insert(woven, t[len])
  return woven
end

local function compile_binop(token, line, lhs, rhs)
  if bitlib and C.BITOPS[token] then
    local bitop = ('require("%s").%s('):format(bitlib, C.BITLIB_METHODS[token])
    return { line, bitop, lhs, line, ',', rhs, line, ')' }
  elseif token == '!=' then
    return { lhs, line, '~=', rhs }
  elseif token == '||' then
    return { lhs, line, 'or', rhs }
  elseif token == '&&' then
    return { lhs, line, 'and', rhs }
  elseif token == '^' then
    return (C.LUA_TARGET == '5.3' or C.LUA_TARGET == '5.3+' or C.LUA_TARGET == '5.4' or C.LUA_TARGET == '5.4+')
      and { lhs, line, token, rhs }
      or { line, 'math.pow(', lhs, ',', rhs, line, ')' }
  elseif token == '//' then
    return (C.LUA_TARGET == '5.3' or C.LUA_TARGET == '5.3+' or C.LUA_TARGET == '5.4' or C.LUA_TARGET == '5.4+')
      and { lhs, line, token, rhs }
      or { line, 'math.floor(', lhs, line, '/', rhs, line, ')' }
  else
    return { lhs, line, token, rhs }
  end
end

-- -----------------------------------------------------------------------------
-- Macros
-- -----------------------------------------------------------------------------

local function List(callback, break_token)
  local list = {}

  repeat
    local item = callback()
    if item then table.insert(list, item) end
  until not branch(',') or (break_token and current_token == break_token)

  return list
end

local function Surround(open_char, close_char, callback)
  expect(open_char)
  local result = callback()
  expect(close_char)
  return result
end

local function SurroundList(open_char, close_char, callback, allow_empty)
  return Surround(open_char, close_char, function()
    if not allow_empty or current_token ~= close_char then
      return List(callback, close_char)
    end
  end)
end

-- -----------------------------------------------------------------------------
-- Partials
-- -----------------------------------------------------------------------------

local function Name(allow_keywords)
  ensure(current_token ~= nil, 'unexpected eof')
  ensure(
    current_token:match('^[_a-zA-Z][_a-zA-Z0-9]*$'),
    ("unexpected token '%s'"):format(current_token)
  )

  if not allow_keywords then
    for i, keyword in pairs(C.KEYWORDS) do
      ensure(current_token ~= keyword, ("unexpected keyword '%s'"):format(current_token))
    end

    if C.LUA_KEYWORDS[current_token] then
      return ('__ERDE_SUBSTITUTE_%s__'):format(consume())
    end
  end

  return consume()
end

local function Destructure()
  local names = {}
  local compile_lines = {}
  local compile_name = new_tmp_name()

  if current_token == '[' then
    local array_index = 0
    SurroundList('[', ']', function()
      local name_line, name = current_line, Name()
      array_index = array_index + 1

      insert(names, name)
      insert(compile_lines, name_line)
      insert(compile_lines, ('local %s = %s[%s]'):format(name, compile_name, array_index))

      if branch('=') then
        insert(compile_lines, ('if %s == nil then %s = '):format(name, name))
        insert(compile_lines, Expr())
        insert(compile_lines, 'end')
      end
    end)
  else
    SurroundList('{', '}', function()
      local key_line, key = current_line, Name()
      local name = branch(':') and Name() or key

      insert(names, name)
      insert(compile_lines, key_line)
      insert(compile_lines, ('local %s = %s.%s'):format(name, compile_name, key))

      if branch('=') then
        insert(compile_lines, ('if %s == nil then %s = '):format(name, name))
        insert(compile_lines, Expr())
        insert(compile_lines, 'end')
      end
    end)
  end

  return {
    names = names,
    compile_name = compile_name,
    compile_lines = compile_lines,
  }
end

local function Var()
  return (current_token == '{' or current_token == '[')
    and Destructure() or Name()
end

local function ReturnList(require_list_parens)
  local compile_lines = {}

  if current_token ~= '(' then
    insert(compile_lines, require_list_parens and Expr() or weave(List(Expr)))
  else
    local look_ahead_limit_token, look_ahead_limit_token_index = look_past_surround()

    if look_ahead_limit_token == '->' or look_ahead_limit_token == '=>' then
      insert(compile_lines, Expr())
    else
      local is_list = false

      for look_ahead_token_index = current_token_index + 1, look_ahead_limit_token_index - 1 do
        local look_ahead_token = tokens[look_ahead_token_index]

        if C.SURROUND_ENDS[look_ahead_token] then
          look_ahead_token, look_ahead_token_index = look_past_surround(look_ahead_token_index)
        end

        if look_ahead_token == ',' then
          is_list = true
          break
        end
      end

      insert(compile_lines, is_list and weave(SurroundList('(', ')', Expr)) or Expr())
    end
  end

  return compile_lines
end

local function Params()
  local compile_lines = {}
  local names = {}
  local has_varargs = false

  SurroundList('(', ')', function()
    if branch('...') then
      has_varargs = true
      insert(names, '...')

      if current_token ~= ')' then
        insert(compile_lines, 'local ' .. Name() .. ' = { ... }')
      end

      branch(',')
      expect(')', true)
    else
      local var = Var()
      local name = type(var) == 'string' and var or var.compile_name
      insert(names, name)

      if branch('=') then
        insert(compile_lines, ('if %s == nil then %s = '):format(name, name))
        insert(compile_lines, Expr())
        insert(compile_lines, 'end')
      end

      if type(var) == 'table' then
        insert(compile_lines, var.compile_lines)
      end
    end
  end, true)

  return { names = names, compile_lines = compile_lines, has_varargs = has_varargs }
end

local function FunctionBlock()
  local old_is_in_module_return_block = is_module_return_block
  local old_break_name = break_name

  is_module_return_block = false
  break_name = nil

  local compile_lines = Surround('{', '}', Block)

  is_module_return_block = old_is_module_return_block
  break_name = old_break_name
  return compile_lines
end

local function LoopBlock()
  local old_break_name = break_name
  local old_has_continue = has_continue

  break_name = new_tmp_name()
  has_continue = false

  local compile_lines = Surround('{', '}', function()
    return Block(true)
  end)

  break_name = old_break_name
  has_continue = old_has_continue
  return compile_lines
end

-- -----------------------------------------------------------------------------
-- Expressions
-- -----------------------------------------------------------------------------

local function ArrowFunction()
  local compile_lines = {}
  local param_names = {}
  local old_is_varargs_block = is_varargs_block

  if current_token == '(' then
    local params = Params()
    is_varargs_block = params.has_varargs
    param_names = params.names
    insert(compile_lines, params.compile_lines)
  else
    local var = Var()
    if type(var) == 'string' then
      insert(param_names, var)
    else
      insert(param_names, var.compile_name)
      insert(compile_lines, var.compile_lines)
    end
  end

  if current_token == '->' then
    consume()
  elseif current_token == '=>' then
    insert(param_names, 1, 'self')
    consume()
  elseif current_token == nil then
    utils.erde_error({
      line = token_lines[current_token_index - 1],
      message = "unexpected eof (expected '->' or '=>')",
    })
  else
    utils.erde_error({
      line = current_line,
      message = ("unexpected token '%s' (expected '->' or '=>')"):format(current_token),
    })
  end

  insert(compile_lines, 1, 'function(' .. concat(param_names, ',') .. ')')

  if current_token == '{' then
    insert(compile_lines, FunctionBlock(has_varargs))
  else
    insert(compile_lines, 'return')
    insert(compile_lines, ReturnList(true))
  end

  is_varargs_block = old_is_varargs_block
  insert(compile_lines, 'end')
  return compile_lines
end

local function IndexChain(allow_arbitrary_expr)
  local compile_lines = {}
  local is_trivial_chain = true
  local has_expr_base = current_token == '('

  if has_expr_base then
    insert(compile_lines, '(')
    insert(compile_lines, Surround('(', ')', Expr))
    insert(compile_lines, ')')
  else
    insert(compile_lines, current_line)
    insert(compile_lines, Name())
  end

  while true do
    if current_token == '.' then
      insert(compile_lines, current_line)
      insert(compile_lines, consume() .. Name(true))
    elseif current_token == '[' then
      insert(compile_lines, current_line)
      insert(compile_lines, '[')
      insert(compile_lines, Surround('[', ']', Expr))
      insert(compile_lines, ']')
    elseif branch(':') then
      insert(compile_lines, current_line)
      insert(compile_lines, ':' .. Name(true))
      expect('(', true)
    -- Use newlines to infer whether the parentheses belong to a function call
    -- or the next statement.
    elseif current_token == '(' and current_line == token_lines[current_token_index - 1] then
      local preceding_compile_lines = compile_lines
      local preceding_compile_lines_len = #preceding_compile_lines
      while type(preceding_compile_lines[preceding_compile_lines_len]) == 'table' do
        preceding_compile_lines = preceding_compile_lines[preceding_compile_lines_len]
        preceding_compile_lines_len = #preceding_compile_lines
      end

      -- Include function call parens on same line as function name to prevent
      -- parsing errors in Lua5.1:
      --    `ambiguous syntax (function call x new statement) near '('`
      preceding_compile_lines[preceding_compile_lines_len] =
        preceding_compile_lines[preceding_compile_lines_len] .. '('

      local args = SurroundList('(', ')', Expr, true)
      if args then insert(compile_lines, weave(args)) end
      insert(compile_lines,  ')')
    else
      break
    end

    is_trivial_chain = false
  end

  if has_expr_base and not allow_arbitrary_expr and is_trivial_chain then
    error() -- internal error
  end

  return compile_lines
end

local function InterpolationString(start_quote, end_quote)
  local compile_lines = {}
  local content_line, content = current_line, consume()
  local is_block_string = start_quote:sub(1, 1) == '['

  if current_token == end_quote then
    -- Handle empty string case exceptionally so we can make assumptions at the
    -- end to simplify excluding empty string concatenations.
    insert(compile_lines, content .. consume())
    return compile_lines
  end

  repeat
    if current_token == '{' then
      if content ~= start_quote then -- only if nonempty
        insert(compile_lines, content_line)
        insert(compile_lines, content .. end_quote)
      end

      insert(compile_lines, { 'tostring(', Surround('{', '}', Expr), ')' })
      content_line, content = current_line, start_quote

      if is_block_string and current_token:sub(1, 1) == '\n' then
        -- Lua ignores the first character in block strings when it is a
        -- newline! We need to make sure we preserve any newline following
        -- an interpolation by inserting a second newline in the compiled code.
        -- @see http://www.lua.org/pil/2.4.html
        content = content .. '\n' .. consume()
      end
    else
      content = content .. consume()
    end
  until current_token == end_quote

  if content ~= start_quote then -- only if nonempty
    insert(compile_lines, content_line)
    insert(compile_lines, content .. end_quote)
  end

  consume() -- end_quote
  return weave(compile_lines, '..')
end

local function Table()
  local compile_lines = {}

  SurroundList('{', '}', function()
    if current_token == '[' then
      insert(compile_lines, '[')
      insert(compile_lines, Surround('[', ']', Expr))
      insert(compile_lines, ']')
      insert(compile_lines, expect('='))
    elseif look_ahead(1) == '=' then
      insert(compile_lines, Name())
      insert(compile_lines, consume()) -- '='
    end

    insert(compile_lines, Expr())
    insert(compile_lines, ',')
  end, true)

  return { '{', compile_lines, '}' }
end

local function Terminal()
  ensure(current_token ~= nil, 'unexpected eof')
  ensure(current_token ~= '...' or is_varargs_block, "cannot use '...' outside a vararg function")

  for _, terminal in pairs(C.TERMINALS) do
    if current_token == terminal then
      return { current_line, consume() }
    end
  end

  if current_token:match('^.?[0-9]') then
    -- Only need to check first couple chars, rest is token care of by tokenizer
    return { current_line, consume() }
  elseif current_token == "'" then
    local quote = consume()
    return current_token == quote -- check empty string
      and { current_line, quote .. consume() }
      or { current_line, quote .. consume() .. consume() }
  elseif current_token == '"' then
    return InterpolationString('"', '"')
  elseif current_token:match('^%[[[=]') then
    return InterpolationString(current_token, current_token:gsub('%[', ']'))
  end

  local next_token = look_ahead(1)
  local is_arrow_function = next_token == '->' or next_token == '=>'

  -- First do a quick check for is_arrow_function (in case of implicit params),
  -- otherwise if surround_end is truthy (possible params), need to check the
  -- next token after. This is _much_ faster than backtracking.
  if not is_arrow_function and C.SURROUND_ENDS[current_token] then
    local past_surround_token = look_past_surround()
    is_arrow_function = past_surround_token == '->' or past_surround_token == '=>'
  end

  if is_arrow_function then
    return ArrowFunction()
  elseif current_token == '{' then
    return Table()
  else
    return IndexChain(true)
  end
end

local function Unop()
  local compile_lines  = {}
  local unop_line, unop = current_line, C.UNOPS[consume()]
  local operand_line, operand = current_line, Expr(unop.prec + 1)

  if unop.token == '~' then
    if (C.LUA_TARGET == '5.1+' or C.LUA_TARGET == '5.2+') and not C.BITLIB then
      utils.erde_error({
        line = unop_line,
        message = 'must use --bitlib for compiling bit operations when targeting 5.1+ or 5.2+',
      })
    end

    local bitop = ('require("%s").%s('):format(bitlib, 'bnot')
    return { unop_line, bitop, operand_line, operand, unop_line, ')' }
  elseif unop.token == '!' then
    return { unop_line, 'not', operand_line, operand }
  else
    return { unop_line, unop.token, operand_line, operand }
  end
end

function Expr(min_prec)
  min_prec = min_prec or 1

  local compile_lines = C.UNOPS[current_token] and Unop() or Terminal()
  local binop = C.BINOPS[current_token]

  while binop and binop.prec >= min_prec do
    local binop_line = current_line
    consume()

    local rhs_min_prec = binop.prec
    if binop.assoc == C.LEFT_ASSOCIATIVE then
      rhs_min_prec = rhs_min_prec + 1
    end

    if C.BITOPS[binop.token] and (C.LUA_TARGET == '5.1+' or C.LUA_TARGET == '5.2+') and not C.BITLIB then
      utils.erde_error({
        line = binop_line,
        message = 'must use --bitlib for compiling bit operations when targeting 5.1+ or 5.2+',
      })
    end

    compile_lines = compile_binop(binop.token, binop_line, compile_lines, Expr(rhs_min_prec))
    binop = C.BINOPS[current_token]
  end

  return compile_lines
end

-- -----------------------------------------------------------------------------
-- Statements
-- -----------------------------------------------------------------------------

local function Assignment(first_id)
  local compile_lines = {}
  local id_list = { first_id }

  while branch(',') do
    local index_chain_line = current_line
    local index_chain = IndexChain()

    if index_chain[#index_chain] == ')' then
      utils.erde_error({
        line = index_chain_line,
        message = 'cannot assign value to function call',
      })
    end

    insert(id_list, index_chain)
  end

  local op_line, op_token = current_line, C.BINOP_ASSIGNMENT_TOKENS[current_token] and consume()
  if C.BITOPS[op_token] and (C.LUA_TARGET == '5.1+' or C.LUA_TARGET == '5.2+') and not C.BITLIB then
    utils.erde_error({
      line = op_line,
      message = 'must use --bitlib for compiling bit operations when targeting 5.1+ or 5.2+',
    })
  end

  expect('=')
  local expr_list = List(Expr)

  if not op_token then
    insert(compile_lines, weave(id_list))
    insert(compile_lines, '=')
    insert(compile_lines, weave(expr_list))
  elseif #id_list == 1 then
    -- Optimize most common use case
    insert(compile_lines, first_id)
    insert(compile_lines, op_line)
    insert(compile_lines, '=')
    insert(compile_lines, compile_binop(op_token, op_line, first_id, expr_list[1]))
  else
    local assignment_names = {}
    local assignment_compile_lines = {}

    for i, id in ipairs(id_list) do
      local assignment_name = new_tmp_name()
      insert(assignment_names, assignment_name)
      insert(assignment_compile_lines, id)
      insert(assignment_compile_lines, '=')
      insert(assignment_compile_lines, compile_binop(op_token, op_line, id, assignment_name))
    end

    insert(compile_lines, 'local')
    insert(compile_lines, concat(assignment_names, ','))
    insert(compile_lines, '=')
    insert(compile_lines, weave(expr_list))
    insert(compile_lines, assignment_compile_lines)
  end

  return compile_lines
end

local function Declaration(scope)
  local names = {}
  local compile_names = {}
  local compile_lines = {}
  local destructure_compile_lines = {}

  if block_depth > 1 and scope == 'module' then
    utils.erde_error({
      line = token_lines[current_token_index - 1],
      message = 'module declarations must appear at the top level',
    })
  end

  if scope ~= 'global' then
    insert(compile_lines, 'local')
  end

  for _, var in ipairs(List(Var)) do
    if type(var) == 'string' then
      insert(names, var)
      insert(compile_names, var)
    else
      insert(compile_names, var.compile_name)
      insert(destructure_compile_lines, var.compile_lines)
      for _, name in ipairs(var.names) do
        insert(names, name)
      end
    end
  end

  if scope == 'module' then
    for _, name in ipairs(names) do
      insert(module_names, name)
    end
  end

  insert(compile_lines, weave(compile_names))

  if current_token == '=' then
    insert(compile_lines, consume())
    insert(compile_lines, weave(List(Expr)))
  end

  insert(compile_lines, destructure_compile_lines)
  return compile_lines
end

local function ForLoop()
  local compile_lines = { consume() }
  local pre_body_compile_lines = {}

  if look_ahead(1) == '=' then
    insert(compile_lines, current_line)
    insert(compile_lines, Name())
    insert(compile_lines, current_line)
    insert(compile_lines, consume())

    local expr_list_line = current_line
    local expr_list = List(Expr)
    local expr_list_len = #expr_list

    if expr_list_len < 2 then
      utils.erde_error({
        line = expr_list_line,
        message = 'missing loop parameters (must supply 2-3 params)',
      })
    elseif expr_list_len > 3 then
      utils.erde_error({
        line = expr_list_line,
        message = 'too many loop parameters (must supply 2-3 params)',
      })
    end

    insert(compile_lines, weave(expr_list))
  else
    local names = {}

    for i, var in ipairs(List(Var)) do
      if type(var) == 'string' then
        insert(names, var)
      else
        insert(names, var.compile_name)
        insert(pre_body_compile_lines, var.compile_lines)
      end
    end

    insert(compile_lines, weave(names))
    insert(compile_lines, expect('in'))

    -- Generic for parses an expression list!
    -- see https://www.lua.org/pil/7.2.html
    -- TODO: only allow max 3 expressions? Job for linter?
    insert(compile_lines, weave(List(Expr)))
  end

  insert(compile_lines, 'do')
  insert(compile_lines, pre_body_compile_lines)
  insert(compile_lines, LoopBlock())
  insert(compile_lines, 'end')
  return compile_lines
end

local function Function(scope)
  local scope_line = token_lines[math.max(1, current_line - 1)]
  local compile_lines = { consume() }
  local signature = Name()
  local is_table_value = current_token == '.'

  while branch('.') do
    signature = signature .. '.' .. Name()
  end

  if branch(':') then
    is_table_value = true
    signature = signature .. ':' .. Name()
  end

  insert(compile_lines, signature)

  if is_table_value and scope ~= nil then
    -- Lua does not allow scope for table functions (ex. `local function a.b()`)
    utils.erde_error({
      line = scope_line,
      message = 'cannot use scopes for table values',
    })
  end

  if not is_table_value and scope ~= 'global' then
    -- Note: This includes when scope is undefined! Default to local scope.
    insert(compile_lines, 1, 'local')
  end

  if scope == 'module' then
    if block_depth > 1 then
      utils.erde_error({
        line = scope_line,
        message = 'module declarations must appear at the top level',
      })
    end

    insert(module_names, signature)
  end

  local params = Params()
  insert(compile_lines, '(' .. concat(params.names, ',') .. ')')
  insert(compile_lines, params.compile_lines)

  local old_is_varargs_block = is_varargs_block
  is_varargs_block = params.has_varargs
  insert(compile_lines, FunctionBlock(params.has_varargs))
  is_varargs_block = old_is_varargs_block

  insert(compile_lines, 'end')
  return compile_lines
end

local function IfElse()
  local compile_lines = {}

  insert(compile_lines, consume())
  insert(compile_lines, Expr())
  insert(compile_lines, 'then')
  insert(compile_lines, Surround('{', '}', Block))

  while current_token == 'elseif' do
    insert(compile_lines, consume())
    insert(compile_lines, Expr())
    insert(compile_lines, 'then')
    insert(compile_lines, Surround('{', '}', Block))
  end

  if current_token == 'else' then
    insert(compile_lines, consume())
    insert(compile_lines, Surround('{', '}', Block))
  end

  insert(compile_lines, 'end')
  return compile_lines
end

local function Return()
  local compile_lines = { current_line, consume() }

  if is_module_return_block then
    has_module_return = true
    if #module_names > 0 then
      utils.erde_error({
        line = token_lines[current_token_index - 1],
        message = "cannot use 'module' declarations w/ 'return'"
      })
    end
  end

  if current_token and current_token ~= '}' then
    insert(compile_lines, ReturnList())
  end

  if block_depth == 1 and current_token then
    utils.erde_error({
      line = current_line,
      message = ("expected '<eof>', got '%s'"):format(current_token),
    })
  elseif block_depth > 1 and current_token ~= '}' then
    utils.erde_error({
      line = current_line,
      message = ("expected '}', got '%s'"):format(current_token),
    })
  end

  return compile_lines
end

-- -----------------------------------------------------------------------------
-- Block
-- -----------------------------------------------------------------------------

function Block(is_loop_block)
  local compile_lines = {}
  local block_start_line = current_line
  block_depth = block_depth + 1

  while current_token ~= nil and current_token ~= '}' do
    if current_token == 'break' then
      ensure(break_name ~= nil, "cannot use 'break' outside of loop")
      insert(compile_lines, current_line)
      insert(compile_lines, consume())
    elseif branch('continue') then
      ensure(break_name ~= nil, "cannot use 'continue' outside of loop")
      has_continue = true

      if C.LUA_TARGET == '5.1' or C.LUA_TARGET == '5.1+' then
        insert(compile_lines, break_name .. ' = true break')
      else
        insert(compile_lines, 'goto ' .. break_name)
      end
    elseif current_token == 'goto' then
      if C.LUA_TARGET == '5.1' or C.LUA_TARGET == '5.1+' then
        utils.erde_error({
          line = current_line,
          message = "'goto' statements only compatibly with lua targets 5.2+, jit",
        })
      end

      insert(compile_lines, current_line)
      insert(compile_lines, consume())
      insert(compile_lines, current_line)
      insert(compile_lines, Name())
    elseif current_token == '::' then
      if C.LUA_TARGET == '5.1' or C.LUA_TARGET == '5.1+' then
        utils.erde_error({
          line = current_line,
          message = "'goto' statements only compatibly with lua targets 5.2+, jit",
        })
      end

      insert(compile_lines, current_line)
      insert(compile_lines, consume() .. Name() .. expect('::'))
    elseif current_token == 'do' then
      insert(compile_lines, consume())
      insert(compile_lines, Surround('{', '}', Block))
      insert(compile_lines, 'end')
    elseif current_token == 'if' then
      insert(compile_lines, IfElse())
    elseif current_token == 'for' then
      insert(compile_lines, ForLoop())
    elseif current_token == 'while' then
      insert(compile_lines, consume())
      insert(compile_lines, Expr())
      insert(compile_lines, 'do')
      insert(compile_lines, LoopBlock())
      insert(compile_lines, 'end')
    elseif current_token == 'repeat' then
      insert(compile_lines, consume())
      insert(compile_lines, LoopBlock())
      insert(compile_lines, expect('until'))
      insert(compile_lines, Expr())
    elseif current_token == 'return' then
      insert(compile_lines, Return())
    elseif current_token == 'function' then
      insert(compile_lines, Function())
    elseif current_token == 'module' and has_module_return then
      utils.erde_error({
        line = current_line,
        message = "cannot use 'module' declarations w/ 'return'"
      })
    elseif current_token == 'local' or current_token == 'global' or current_token == 'module' then
      local scope = consume()
      insert(compile_lines, current_token == 'function' and Function(scope) or Declaration(scope))
    else
      local index_chain = IndexChain()
      local last_index_chain_token = index_chain[#index_chain]

      if last_index_chain_token == ')' or last_index_chain_token == ');' then
        -- Allow function calls as standalone statements
        insert(compile_lines, index_chain)
      else
        insert(compile_lines, Assignment(index_chain))
      end
    end

    if current_token == ';' then
      insert(compile_lines, consume())
    elseif current_token == '(' then
      -- Add semi-colon to prevent ambiguous Lua code
      insert(compile_lines, ';')
    end
  end

  block_depth = block_depth - 1

  if is_loop_block and break_name and has_continue then
    if C.LUA_TARGET == '5.1' or C.LUA_TARGET == '5.1+' then
      insert(compile_lines, 1, ('local %s = false repeat'):format(break_name))
      insert(
        compile_lines,
        ('%s = true until true if not %s then break end'):format(break_name, break_name)
      )
    else
      insert(compile_lines, '::' .. break_name .. '::')
    end
  end

  return compile_lines
end

-- -----------------------------------------------------------------------------
-- Main
-- -----------------------------------------------------------------------------

return function(text)
  tokens, token_lines = tokenize(text)
  current_token, current_token_index = tokens[1], 1
  current_line = token_lines[1]

  block_depth = 0
  is_module_return_block = true
  has_module_return = false
  has_continue = false
  is_varargs_block = true
  tmp_name_counter = 1
  module_names = {}

  bitlib = C.BITLIB
    or (C.LUA_TARGET == '5.1' and 'bit') -- Mike Pall's LuaBitOp
    or (C.LUA_TARGET == 'jit' and 'bit') -- Mike Pall's LuaBitOp
    or (C.LUA_TARGET == '5.2' and 'bit32') -- Lua 5.2's builtin bit32 library

  -- Check for empty file or file w/ only comments
  if current_token == nil then
    return ''
  end

  local compile_lines = {}

  if current_token:match('^#!') then
    insert(compile_lines, consume())
  end

  insert(compile_lines, Block())
  if current_token then
    utils.erde_error({
      line = current_line,
      message = ("unexpected token '%s'"):format(current_token)
    })
  end

  if #module_names > 0 then
    local module_table_elements = {}

    for i, module_name in ipairs(module_names) do
      insert(module_table_elements, module_name .. '=' .. module_name)
    end

    insert(compile_lines, ('return { %s }'):format(concat(module_table_elements, ',')))
  end

  -- Free resources (potentially large tables)
  tokens, token_lines = nil, nil

  local collapsed_compile_lines = {}
  local collapsed_compile_line_counter = 0
  local source_map = {}

  -- Assign compiled lines with no source to the last known source line. We do
  -- this because Lua may give an error at the line of the _next_ token in
  -- certain cases. For example, the following will give an error at line 3,
  -- instead of line 2 where the nil index actually occurs:
  --   local x = nil
  --   print(x.a
  --   )
  local source_line = 1

  local function collect_lines(lines)
    for _, line in ipairs(lines) do
      if type(line) == 'number' then
        source_line = line
      elseif type(line) == 'string' then
        insert(collapsed_compile_lines, line)
        collapsed_compile_line_counter = collapsed_compile_line_counter + 1
        source_map[collapsed_compile_line_counter] = source_line
      else
        collect_lines(line)
      end
    end
  end

  collect_lines(compile_lines)
  insert(collapsed_compile_lines, C.COMPILED_FOOTER_COMMENT)
  return concat(collapsed_compile_lines, '\n'), source_map
end
