local config = require("erde.config")
local BINOP_ASSIGNMENT_TOKENS, BINOPS, BITOPS, BITLIB_METHODS, COMPILED_FOOTER_COMMENT, DIGIT, KEYWORDS, LEFT_ASSOCIATIVE, LUA_KEYWORDS, SURROUND_ENDS, TERMINALS, TOKEN_TYPES, UNOPS, VERSION
local __ERDE_TMP_4__ = require("erde.constants")
BINOP_ASSIGNMENT_TOKENS = __ERDE_TMP_4__.BINOP_ASSIGNMENT_TOKENS
BINOPS = __ERDE_TMP_4__.BINOPS
BITOPS = __ERDE_TMP_4__.BITOPS
BITLIB_METHODS = __ERDE_TMP_4__.BITLIB_METHODS
COMPILED_FOOTER_COMMENT = __ERDE_TMP_4__.COMPILED_FOOTER_COMMENT
DIGIT = __ERDE_TMP_4__.DIGIT
KEYWORDS = __ERDE_TMP_4__.KEYWORDS
LEFT_ASSOCIATIVE = __ERDE_TMP_4__.LEFT_ASSOCIATIVE
LUA_KEYWORDS = __ERDE_TMP_4__.LUA_KEYWORDS
SURROUND_ENDS = __ERDE_TMP_4__.SURROUND_ENDS
TERMINALS = __ERDE_TMP_4__.TERMINALS
TOKEN_TYPES = __ERDE_TMP_4__.TOKEN_TYPES
UNOPS = __ERDE_TMP_4__.UNOPS
VERSION = __ERDE_TMP_4__.VERSION
local table
local __ERDE_TMP_7__ = require("erde.stdlib")
table = __ERDE_TMP_7__.table
local tokenize = require("erde.tokenize")
local get_source_alias
local __ERDE_TMP_12__ = require("erde.utils")
get_source_alias = __ERDE_TMP_12__.get_source_alias
local unpack = table.unpack or unpack
local arrow_function, block, expression, statement
local tokens
local current_token_index
local current_token
local block_depth
local tmp_name_counter
local break_name
local has_continue
local has_module_declarations
local is_module_return_block, module_return_line
local is_varargs_block
local block_declarations, block_declaration_stack
local goto_jumps, goto_labels
local alias
local lua_target
local bitexpr
local function throw(message, line)
	if line == nil then
		line = current_token.line
	end
	error(tostring(alias) .. ":" .. tostring(line) .. ": " .. tostring(message), 0)
end
local function add_block_declaration(var, scope, stack_depth)
	if stack_depth == nil then
		stack_depth = block_depth
	end
	if block_declaration_stack[stack_depth] == nil then
		for i = stack_depth - 1, 1, -1 do
			local parent_block_declarations = block_declaration_stack[i]
			if parent_block_declarations ~= nil then
				block_declaration_stack[stack_depth] = table.shallowcopy(parent_block_declarations)
				break
			end
		end
	end
	local target_block_declarations = block_declaration_stack[stack_depth]
	if type(var) == "string" then
		target_block_declarations[var] = scope
	else
		for _, declaration_name in ipairs(var.declaration_names) do
			target_block_declarations[declaration_name] = scope
		end
	end
end
local function consume()
	local consumed_token_value = current_token.value
	current_token_index = current_token_index + 1
	current_token = tokens[current_token_index]
	return consumed_token_value
end
local function branch(token)
	if token == current_token.value then
		consume()
		return true
	end
end
local function expect(token, should_consume)
	if current_token.type == TOKEN_TYPES.EOF then
		throw("unexpected eof (expected " .. tostring(token) .. ")")
	end
	if token ~= current_token.value then
		throw("expected '" .. tostring(token) .. "' got '" .. tostring(current_token.value) .. "'")
	end
	if should_consume then
		return consume()
	end
end
local function look_past_surround(token_start_index)
	if token_start_index == nil then
		token_start_index = current_token_index
	end
	local surround_start_token = tokens[token_start_index]
	local surround_end = SURROUND_ENDS[surround_start_token.value]
	local surround_depth = 1
	local look_ahead_token_index = token_start_index + 1
	local look_ahead_token = tokens[look_ahead_token_index]
	repeat
		if look_ahead_token.type == TOKEN_TYPES.EOF then
			throw("unexpected eof, missing '" .. tostring(surround_end) .. "'", surround_start_token.line)
		end
		if look_ahead_token.value == surround_start_token.value then
			surround_depth = surround_depth + 1
		elseif look_ahead_token.value == surround_end then
			surround_depth = surround_depth - 1
		end
		look_ahead_token_index = look_ahead_token_index + 1
		look_ahead_token = tokens[look_ahead_token_index]
	until surround_depth == 0
	return look_ahead_token, look_ahead_token_index
end
local function new_tmp_name()
	tmp_name_counter = tmp_name_counter + 1
	return "__ERDE_TMP_" .. tostring(tmp_name_counter) .. "__"
end
local function get_compile_name(name, scope)
	if scope == "module" then
		if LUA_KEYWORDS[name] then
			return "_MODULE['" .. tostring(name) .. "']"
		else
			return "_MODULE." .. name
		end
	elseif scope == "global" then
		if LUA_KEYWORDS[name] then
			return "_G['" .. tostring(name) .. "']"
		else
			return "_G." .. name
		end
	end
	if LUA_KEYWORDS[name] then
		return tostring(name) .. "_"
	else
		return name
	end
end
local function weave(t, separator)
	if separator == nil then
		separator = ","
	end
	local woven = {}
	local len = #t
	for i = 1, len - 1 do
		table.insert(woven, t[i])
		if type(t[i]) ~= "number" then
			table.insert(woven, separator)
		end
	end
	table.insert(woven, t[len])
	return woven
end
local function compile_binop(op_token, op_line, lhs, rhs)
	local needs_floor_division_polyfill = (
		op_token == "//"
		and lua_target ~= "5.3"
		and lua_target ~= "5.4"
		and lua_target ~= "5.3+"
		and lua_target ~= "5.4+"
	)
	if needs_floor_division_polyfill then
		return {
			op_line,
			"math.floor(",
			lhs,
			op_line,
			"/",
			rhs,
			")",
		}
	elseif bitexpr and BITOPS[op_token] then
		return {
			op_line,
			"((" .. tostring(bitexpr) .. ")." .. tostring(BITLIB_METHODS[op_token]) .. "(",
			lhs,
			",",
			rhs,
			"))",
		}
	elseif op_token == "!=" then
		return {
			lhs,
			"~=",
			rhs,
		}
	elseif op_token == "==" then
		return {
			lhs,
			op_token,
			rhs,
		}
	elseif op_token == "||" then
		return {
			lhs,
			"or",
			rhs,
		}
	elseif op_token == "&&" then
		return {
			lhs,
			"and",
			rhs,
		}
	else
		return {
			lhs,
			op_line,
			op_token,
			rhs,
		}
	end
end
local function list(callback, break_token)
	local list = {}
	repeat
		table.insert(list, callback() or nil)
	until not branch(",") or (break_token and current_token.value == break_token)
	return list
end
local function surround(open_char, close_char, callback)
	expect(open_char, true)
	local result = callback()
	expect(close_char, true)
	return result
end
local function surround_list(open_char, close_char, allow_empty, callback)
	return surround(open_char, close_char, function()
		if current_token.value ~= close_char or not allow_empty then
			return list(callback, close_char)
		else
			return {}
		end
	end)
end
local function name()
	if current_token.type == TOKEN_TYPES.EOF then
		throw("unexpected eof")
	end
	if current_token.type ~= TOKEN_TYPES.WORD then
		throw("unexpected token '" .. tostring(current_token.value) .. "'")
	end
	if KEYWORDS[current_token.value] ~= nil then
		throw("unexpected keyword '" .. tostring(current_token.value) .. "'")
	end
	if TERMINALS[current_token.value] ~= nil then
		throw("unexpected builtin '" .. tostring(current_token.value) .. "'")
	end
	return consume()
end
local function array_destructure(scope)
	local compile_lines = {}
	local compile_name = new_tmp_name()
	local declaration_names = {}
	local array_index = 0
	table.insert(compile_lines, current_token.line)
	surround_list("[", "]", false, function()
		array_index = array_index + 1
		local declaration_name = name()
		table.insert(declaration_names, declaration_name)
		local assignment_name = get_compile_name(declaration_name, scope)
		table.insert(
			compile_lines,
			tostring(assignment_name) .. " = " .. tostring(compile_name) .. "[" .. tostring(array_index) .. "]"
		)
		if branch("=") then
			table.insert(
				compile_lines,
				"if " .. tostring(assignment_name) .. " == nil then " .. tostring(assignment_name) .. " = "
			)
			table.insert(compile_lines, expression())
			table.insert(compile_lines, "end")
		end
	end)
	return {
		compile_lines = compile_lines,
		compile_name = compile_name,
		declaration_names = declaration_names,
	}
end
local function map_destructure(scope)
	local compile_lines = {}
	local compile_name = new_tmp_name()
	local declaration_names = {}
	table.insert(compile_lines, current_token.line)
	surround_list("{", "}", false, function()
		local key = name()
		local declaration_name = branch(":") and name() or key
		table.insert(declaration_names, declaration_name)
		local assignment_name = get_compile_name(declaration_name, scope)
		if LUA_KEYWORDS[declaration_name] then
			table.insert(
				compile_lines,
				tostring(assignment_name) .. " = " .. tostring(compile_name) .. "['" .. tostring(key) .. "']"
			)
		else
			table.insert(
				compile_lines,
				tostring(assignment_name) .. " = " .. tostring(compile_name) .. "." .. tostring(key)
			)
		end
		if branch("=") then
			table.insert(
				compile_lines,
				"if " .. tostring(assignment_name) .. " == nil then " .. tostring(assignment_name) .. " = "
			)
			table.insert(compile_lines, expression())
			table.insert(compile_lines, "end")
		end
	end)
	return {
		compile_lines = compile_lines,
		compile_name = compile_name,
		declaration_names = declaration_names,
	}
end
local function variable(scope)
	if scope == nil then
		scope = "local"
	end
	if current_token.value == "[" then
		return array_destructure(scope)
	elseif current_token.value == "{" then
		return map_destructure(scope)
	else
		return name()
	end
end
local function bracket_index(index_chain_state)
	local compile_lines = {
		current_token.line,
		"[",
		surround("[", "]", expression),
		"]",
	}
	index_chain_state.final_base_compile_lines = table.shallowcopy(index_chain_state.compile_lines)
	index_chain_state.final_index_compile_lines = compile_lines
	table.insert(index_chain_state.compile_lines, compile_lines)
end
local function dot_index(index_chain_state)
	local compile_lines = {
		current_token.line,
	}
	consume()
	local key = name()
	if LUA_KEYWORDS[key] then
		table.insert(compile_lines, "['" .. tostring(key) .. "']")
	else
		table.insert(compile_lines, "." .. key)
	end
	index_chain_state.final_base_compile_lines = table.shallowcopy(index_chain_state.compile_lines)
	index_chain_state.final_index_compile_lines = compile_lines
	table.insert(index_chain_state.compile_lines, compile_lines)
end
local function method_index(index_chain_state)
	table.insert(index_chain_state.compile_lines, current_token.line)
	consume()
	local method_name = name()
	local method_parameters = surround_list("(", ")", true, expression)
	if not LUA_KEYWORDS[method_name] then
		table.insert(index_chain_state.compile_lines, ":" .. tostring(method_name) .. "(")
		table.insert(index_chain_state.compile_lines, weave(method_parameters))
		table.insert(index_chain_state.compile_lines, ")")
	elseif index_chain_state.has_trivial_base and index_chain_state.chain_len == 0 then
		table.insert(index_chain_state.compile_lines, "['" .. tostring(method_name) .. "'](")
		table.insert(method_parameters, 1, index_chain_state.base_compile_lines)
		table.insert(index_chain_state.compile_lines, weave(method_parameters))
		table.insert(index_chain_state.compile_lines, ")")
	else
		index_chain_state.needs_block_compile = true
		table.insert(index_chain_state.block_compile_lines, index_chain_state.block_compile_name .. "=")
		table.insert(index_chain_state.block_compile_lines, index_chain_state.compile_lines)
		table.insert(method_parameters, 1, index_chain_state.block_compile_name)
		index_chain_state.compile_lines = {
			tostring(index_chain_state.block_compile_name) .. "['" .. tostring(method_name) .. "'](",
			weave(method_parameters),
			")",
		}
	end
end
local function function_call_index(index_chain_state)
	local preceding_compile_lines = index_chain_state.compile_lines
	local preceding_compile_lines_len = #preceding_compile_lines
	while type(preceding_compile_lines[preceding_compile_lines_len]) == "table" do
		preceding_compile_lines = preceding_compile_lines[preceding_compile_lines_len]
		preceding_compile_lines_len = #preceding_compile_lines
	end
	preceding_compile_lines[preceding_compile_lines_len] = preceding_compile_lines[preceding_compile_lines_len] .. "("
	table.insert(index_chain_state.compile_lines, weave(surround_list("(", ")", true, expression)))
	table.insert(index_chain_state.compile_lines, ")")
end
local function index_chain(options)
	local block_compile_name = new_tmp_name()
	local index_chain_state = {
		base_compile_lines = options.base_compile_lines,
		compile_lines = {
			options.base_compile_lines,
		},
		has_trivial_base = options.has_trivial_base,
		chain_len = 0,
		is_function_call = false,
		needs_block_compile = false,
		block_compile_name = block_compile_name,
		block_compile_lines = {
			"local " .. block_compile_name,
		},
		final_base_compile_lines = options.base_compile_lines,
		final_index_compile_lines = {},
	}
	if options.wrap_base_compile_lines then
		table.insert(index_chain_state.compile_lines, 1, "(")
		table.insert(index_chain_state.compile_lines, ")")
	end
	while true do
		if current_token.value == "(" and current_token.line == tokens[current_token_index - 1].line then
			index_chain_state.is_function_call = true
			function_call_index(index_chain_state)
		elseif current_token.value == "[" then
			index_chain_state.is_function_call = false
			bracket_index(index_chain_state)
		elseif current_token.value == "." then
			index_chain_state.is_function_call = false
			dot_index(index_chain_state)
		elseif current_token.value == ":" then
			index_chain_state.is_function_call = true
			method_index(index_chain_state)
		else
			break
		end
		index_chain_state.chain_len = index_chain_state.chain_len + 1
	end
	if options.require_chain and index_chain_state.chain_len == 0 then
		if current_token.type == TOKEN_TYPES.EOF then
			throw("unexpected eof")
		else
			throw("unexpected token '" .. tostring(current_token.value) .. "'")
		end
	end
	if index_chain_state.chain_len == 0 then
		index_chain_state.compile_lines = options.base_compile_lines
	end
	return index_chain_state
end
local function single_quote_string()
	consume()
	if current_token.type == TOKEN_TYPES.SINGLE_QUOTE_STRING then
		return {
			current_token.line,
			"'" .. consume(),
		}
	else
		return {
			current_token.line,
			"'" .. consume() .. consume(),
		}
	end
end
local function double_quote_string()
	local double_quote_string_line = current_token.line
	local has_interpolation = false
	consume()
	if current_token.type == TOKEN_TYPES.DOUBLE_QUOTE_STRING then
		return {
			double_quote_string_line,
			'"' .. consume(),
		}, has_interpolation
	end
	local compile_lines = {}
	local content = ""
	repeat
		if current_token.type == TOKEN_TYPES.INTERPOLATION then
			has_interpolation = true
			if content ~= "" then
				table.insert(compile_lines, '"' .. content .. '"')
			end
			table.insert(compile_lines, {
				"tostring(",
				surround("{", "}", expression),
				")",
			})
			content = ""
		else
			content = content .. (consume())
		end
	until current_token.type == TOKEN_TYPES.DOUBLE_QUOTE_STRING
	if content ~= "" then
		table.insert(compile_lines, '"' .. content .. '"')
	end
	consume()
	return {
		double_quote_string_line,
		weave(compile_lines, ".."),
	}, has_interpolation
end
local function block_string()
	local block_string_line = current_token.line
	local has_interpolation = false
	local start_quote = "[" .. current_token.equals .. "["
	local end_quote = "]" .. current_token.equals .. "]"
	consume()
	if current_token.type == TOKEN_TYPES.BLOCK_STRING then
		consume()
		return {
			block_string_line,
			start_quote .. end_quote,
		}, has_interpolation
	end
	local compile_lines = {}
	local content = ""
	repeat
		if current_token.type == TOKEN_TYPES.INTERPOLATION then
			has_interpolation = true
			if content ~= "" then
				table.insert(compile_lines, start_quote .. content .. end_quote)
			end
			table.insert(compile_lines, {
				"tostring(",
				surround("{", "}", expression),
				")",
			})
			content = ""
			if current_token.value:sub(1, 1) == "\n" then
				content = content .. ("\n" .. consume())
			end
		else
			content = content .. (consume())
		end
	until current_token.type == TOKEN_TYPES.BLOCK_STRING
	if content ~= "" then
		table.insert(compile_lines, start_quote .. content .. end_quote)
	end
	consume()
	return {
		block_string_line,
		weave(compile_lines, ".."),
	}, has_interpolation
end
local function table_constructor()
	local table_constructor_line = current_token.line
	local compile_lines = {}
	surround_list("{", "}", true, function()
		local next_token = tokens[current_token_index + 1]
		if current_token.value == "[" then
			table.insert(compile_lines, "[")
			table.insert(compile_lines, surround("[", "]", expression))
			table.insert(compile_lines, "]")
			table.insert(compile_lines, expect("=", true))
		elseif next_token.type == TOKEN_TYPES.SYMBOL and next_token.value == "=" then
			local key = name()
			if LUA_KEYWORDS[key] then
				table.insert(compile_lines, "['" .. tostring(key) .. "']" .. consume())
			else
				table.insert(compile_lines, key .. consume())
			end
		end
		table.insert(compile_lines, expression())
		table.insert(compile_lines, ",")
	end)
	return {
		table_constructor_line,
		"{",
		compile_lines,
		"}",
	}
end
local function return_list()
	local look_ahead_limit_token, look_ahead_limit_token_index = look_past_surround()
	if look_ahead_limit_token.value == "->" or look_ahead_limit_token.value == "=>" then
		return arrow_function()
	end
	local look_ahead_token_index = current_token_index + 1
	local look_ahead_token = tokens[look_ahead_token_index]
	while look_ahead_token_index < look_ahead_limit_token_index do
		if look_ahead_token.type == TOKEN_TYPES.SYMBOL and SURROUND_ENDS[look_ahead_token.value] then
			look_ahead_token, look_ahead_token_index = look_past_surround(look_ahead_token_index)
		elseif look_ahead_token.type == TOKEN_TYPES.SYMBOL and look_ahead_token.value == "," then
			return weave(surround_list("(", ")", false, expression))
		else
			look_ahead_token_index = look_ahead_token_index + 1
			look_ahead_token = tokens[look_ahead_token_index]
		end
	end
	return expression()
end
local function block_return()
	if is_module_return_block then
		module_return_line = current_token.line
	end
	local compile_lines = {
		consume(),
	}
	if block_depth == 1 then
		if current_token.type ~= TOKEN_TYPES.EOF then
			if current_token.value == "(" then
				table.insert(compile_lines, return_list())
			else
				table.insert(compile_lines, weave(list(expression)))
			end
		end
		if current_token.type ~= TOKEN_TYPES.EOF then
			throw("expected '<eof>', got '" .. tostring(current_token.value) .. "'")
		end
	else
		if current_token.value ~= "}" then
			if current_token.value == "(" then
				table.insert(compile_lines, return_list())
			else
				table.insert(compile_lines, weave(list(expression)))
			end
		end
		if current_token.value ~= "}" then
			throw("expected '}', got '" .. tostring(current_token.value) .. "'")
		end
	end
	return compile_lines
end
local function parameters()
	local compile_lines = {}
	local compile_names = {}
	local has_varargs = false
	surround_list("(", ")", true, function()
		if branch("...") then
			has_varargs = true
			table.insert(compile_names, "...")
			if current_token.type == TOKEN_TYPES.WORD then
				local varargs_name = name()
				table.insert(compile_lines, "local " .. tostring(get_compile_name(varargs_name)) .. " = { ... }")
				add_block_declaration(varargs_name, "local", block_depth + 1)
			end
			branch(",")
			expect(")")
		else
			local var = variable()
			add_block_declaration(var, "local", block_depth + 1)
			local compile_name = type(var) == "string" and get_compile_name(var) or var.compile_name
			table.insert(compile_names, compile_name)
			if branch("=") then
				table.insert(
					compile_lines,
					"if " .. tostring(compile_name) .. " == nil then " .. tostring(compile_name) .. " = "
				)
				table.insert(compile_lines, expression())
				table.insert(compile_lines, "end")
			end
			if type(var) == "table" then
				table.insert(
					compile_lines,
					"local " .. table.concat(table.map(var.declaration_names, get_compile_name), ",")
				)
				table.insert(compile_lines, var.compile_lines)
			end
		end
	end)
	return {
		compile_lines = compile_lines,
		compile_names = compile_names,
		has_varargs = has_varargs,
	}
end
local function function_block()
	local old_is_module_return_block = is_module_return_block
	local old_break_name = break_name
	is_module_return_block = false
	break_name = nil
	local compile_lines = block()
	is_module_return_block = old_is_module_return_block
	break_name = old_break_name
	return compile_lines
end
function arrow_function()
	local old_is_varargs_block = is_varargs_block
	local arrow_function_line = current_token.line
	local param_compile_lines = {}
	local param_compile_names = {}
	if current_token.value == "(" then
		local params = parameters()
		table.insert(param_compile_lines, params.compile_lines)
		is_varargs_block = params.has_varargs
		param_compile_names = params.compile_names
	else
		is_varargs_block = false
		local var = variable()
		add_block_declaration(var, "local", block_depth + 1)
		if type(var) == "string" then
			table.insert(param_compile_names, get_compile_name(var))
		else
			table.insert(param_compile_names, var.compile_name)
			table.insert(
				param_compile_lines,
				"local " .. table.concat(table.map(var.declaration_names, get_compile_name), ",")
			)
			table.insert(param_compile_lines, var.compile_lines)
		end
	end
	if current_token.value == "->" then
		consume()
	elseif current_token.value == "=>" then
		table.insert(param_compile_names, 1, "self")
		consume()
	elseif current_token.type == TOKEN_TYPES.EOF then
		throw("unexpected eof (expected '->' or '=>')")
	else
		throw("unexpected token '" .. tostring(current_token.value) .. "' (expected '->' or '=>')")
	end
	local compile_lines = {
		arrow_function_line,
		"function(" .. tostring(table.concat(param_compile_names, ",")) .. ")",
		param_compile_lines,
	}
	if current_token.value == "{" then
		table.insert(compile_lines, surround("{", "}", function_block))
	else
		table.insert(compile_lines, "return")
		local old_block_declarations = block_declarations
		block_depth = block_depth + 1
		block_declaration_stack[block_depth] = block_declaration_stack[block_depth] or {}
		block_declarations = block_declaration_stack[block_depth]
		if current_token.value == "(" then
			table.insert(compile_lines, return_list())
		else
			table.insert(compile_lines, expression())
		end
		block_declarations = old_block_declarations
		block_declaration_stack[block_depth] = nil
		block_depth = block_depth - 1
	end
	table.insert(compile_lines, "end")
	is_varargs_block = old_is_varargs_block
	return compile_lines
end
local function function_signature(scope)
	local base_name = name()
	if (current_token.value == "." or current_token.value == ":") and scope ~= nil then
		throw("cannot use scopes for table values", current_token.line)
	end
	if scope == "module" or scope == "global" then
		block_declarations[base_name] = scope
	end
	local signature = get_compile_name(base_name, scope or block_declarations[base_name])
	local needs_label_assignment = false
	local needs_self_injection = false
	while branch(".") do
		local key = name()
		if LUA_KEYWORDS[key] then
			needs_label_assignment = true
			signature = signature .. ("['" .. tostring(key) .. "']")
		else
			signature = signature .. ("." .. key)
		end
	end
	if branch(":") then
		local key = name()
		if LUA_KEYWORDS[key] then
			needs_label_assignment = true
			needs_self_injection = true
			signature = signature .. ("['" .. tostring(key) .. "']")
		else
			signature = signature .. (":" .. key)
		end
	end
	return {
		signature = signature,
		needs_label_assignment = needs_label_assignment,
		needs_self_injection = needs_self_injection,
	}
end
local function function_declaration(scope)
	local compile_lines = {
		current_token.line,
	}
	consume()
	local signature, needs_label_assignment, needs_self_injection
	local __ERDE_TMP_979__ = function_signature(scope)
	signature = __ERDE_TMP_979__.signature
	needs_label_assignment = __ERDE_TMP_979__.needs_label_assignment
	needs_self_injection = __ERDE_TMP_979__.needs_self_injection
	if scope == "local" then
		table.insert(compile_lines, "local")
	end
	if needs_label_assignment then
		table.insert(compile_lines, signature)
		table.insert(compile_lines, "=")
		table.insert(compile_lines, "function")
	else
		table.insert(compile_lines, "function")
		table.insert(compile_lines, signature)
	end
	local params = parameters()
	if needs_self_injection then
		table.insert(params.compile_names, "self")
	end
	table.insert(compile_lines, "(" .. table.concat(params.compile_names, ",") .. ")")
	table.insert(compile_lines, params.compile_lines)
	local old_is_varargs_block = is_varargs_block
	is_varargs_block = params.has_varargs
	table.insert(compile_lines, surround("{", "}", function_block))
	is_varargs_block = old_is_varargs_block
	table.insert(compile_lines, "end")
	return compile_lines
end
local function index_chain_expression(options)
	local index_chain = index_chain(options)
	if index_chain.needs_block_compile then
		return {
			"(function()",
			index_chain.block_compile_lines,
			"return",
			index_chain.compile_lines,
			"end)()",
		}
	else
		return index_chain.compile_lines
	end
end
local function terminal_expression()
	if current_token.type == TOKEN_TYPES.NUMBER then
		return {
			current_token.line,
			consume(),
		}
	elseif current_token.type == TOKEN_TYPES.SINGLE_QUOTE_STRING then
		return index_chain_expression({
			base_compile_lines = single_quote_string(),
			has_trivial_base = true,
			wrap_base_compile_lines = true,
		})
	elseif current_token.type == TOKEN_TYPES.DOUBLE_QUOTE_STRING then
		local compile_lines, has_interpolation = double_quote_string()
		return index_chain_expression({
			base_compile_lines = compile_lines,
			has_trivial_base = not has_interpolation,
			wrap_base_compile_lines = true,
		})
	elseif current_token.type == TOKEN_TYPES.BLOCK_STRING then
		local compile_lines, has_interpolation = block_string()
		return index_chain_expression({
			base_compile_lines = compile_lines,
			has_trivial_base = not has_interpolation,
			wrap_base_compile_lines = true,
		})
	end
	if TERMINALS[current_token.value] then
		if current_token.value == "..." and not is_varargs_block then
			throw("cannot use '...' outside a vararg function")
		end
		return {
			current_token.line,
			consume(),
		}
	end
	local next_token = tokens[current_token_index + 1]
	local is_arrow_function = (
		next_token.type == TOKEN_TYPES.SYMBOL and (next_token.value == "->" or next_token.value == "=>")
	)
	if not is_arrow_function and SURROUND_ENDS[current_token.value] then
		local past_surround_token = look_past_surround()
		is_arrow_function = (
			past_surround_token.type == TOKEN_TYPES.SYMBOL
			and (past_surround_token.value == "->" or past_surround_token.value == "=>")
		)
	end
	if is_arrow_function then
		return arrow_function()
	elseif current_token.value == "{" then
		return table_constructor()
	elseif current_token.value == "(" then
		return index_chain_expression({
			base_compile_lines = {
				current_token.line,
				"(",
				surround("(", ")", expression),
				")",
			},
		})
	else
		local base_name_line, base_name = current_token.line, name()
		return index_chain_expression({
			base_compile_lines = {
				base_name_line,
				get_compile_name(base_name, block_declarations[base_name]),
			},
			has_trivial_base = true,
		})
	end
end
local function unop_expression()
	local unop_line, unop = current_token.line, UNOPS[consume()]
	local operand = expression(unop.prec + 1)
	if unop.token == "!" then
		return {
			"not",
			operand,
		}
	elseif unop.token ~= "~" then
		return {
			unop_line,
			unop.token,
			operand,
		}
	elseif bitexpr then
		return {
			unop_line,
			"((" .. tostring(bitexpr) .. ").bnot(",
			operand,
			"))",
		}
	elseif lua_target == "5.1+" or lua_target == "5.2+" then
		throw("must specify bitexpr or bitlib for compiling bit operations when targeting 5.1+ or 5.2+", unop_line)
	else
		return {
			unop_line,
			unop.token,
			operand,
		}
	end
end
function expression(min_prec)
	if min_prec == nil then
		min_prec = 1
	end
	if current_token.type == TOKEN_TYPES.EOF then
		throw("unexpected eof (expected expression)")
	end
	local compile_lines = UNOPS[current_token.value] and unop_expression() or terminal_expression()
	local binop_line, binop = current_token.line, BINOPS[current_token.value]
	while binop and binop.prec >= min_prec do
		if BITOPS[binop.token] and (lua_target == "5.1+" or lua_target == "5.2+") and not bitexpr then
			throw("must specify bitexpr or bitlib for compiling bit operations when targeting 5.1+ or 5.2+", binop_line)
		end
		consume()
		if binop.token == "~" and current_token.value == "=" then
			throw("unexpected token '~=', did you mean '!='?")
		end
		local operand = binop.assoc == LEFT_ASSOCIATIVE and expression(binop.prec + 1) or expression(binop.prec)
		compile_lines = compile_binop(binop.token, binop_line, compile_lines, operand)
		binop_line, binop = current_token.line, BINOPS[current_token.value]
	end
	return compile_lines
end
function block()
	local old_block_declarations = block_declarations
	block_depth = block_depth + 1
	block_declaration_stack[block_depth] = block_declaration_stack[block_depth]
		or (table.shallowcopy(block_declaration_stack[block_depth - 1]))
	block_declarations = block_declaration_stack[block_depth]
	local compile_lines = {}
	while current_token.value ~= "}" do
		table.insert(compile_lines, statement())
	end
	block_declarations = old_block_declarations
	block_declaration_stack[block_depth] = nil
	block_depth = block_depth - 1
	return compile_lines
end
local function do_block()
	return {
		consume(),
		surround("{", "}", block),
		"end",
	}
end
local function loop_block()
	local old_break_name = break_name
	local old_has_continue = has_continue
	break_name = new_tmp_name()
	has_continue = false
	local compile_lines = block()
	if has_continue then
		if lua_target == "5.1" or lua_target == "5.1+" then
			table.insert(compile_lines, 1, "local " .. tostring(break_name) .. " = true repeat")
			table.insert(
				compile_lines,
				tostring(break_name) .. " = false until true if " .. tostring(break_name) .. " then break end"
			)
		else
			table.insert(compile_lines, "::" .. tostring(break_name) .. "::")
		end
	end
	break_name = old_break_name
	has_continue = old_has_continue
	return compile_lines
end
local function loop_break()
	consume()
	if break_name == nil then
		throw("cannot use 'break' outside of loop")
	end
	if lua_target == "5.1" or lua_target == "5.1+" or lua_target == "jit" then
		if current_token.value ~= "}" then
			throw("expected '}', got '" .. tostring(current_token.value) .. "'")
		end
	end
	return "break"
end
local function loop_continue()
	if break_name == nil then
		throw("cannot use 'continue' outside of loop")
	end
	has_continue = true
	consume()
	if lua_target == "5.1" or lua_target == "5.1+" then
		return tostring(break_name) .. " = false do break end"
	else
		return "goto " .. tostring(break_name)
	end
end
local function for_loop()
	local compile_lines = {}
	local pre_body_compile_lines = {}
	table.insert(compile_lines, consume())
	local next_token = tokens[current_token_index + 1]
	if next_token.type == TOKEN_TYPES.SYMBOL and next_token.value == "=" then
		local loop_name = name()
		add_block_declaration(loop_name, "local", block_depth + 1)
		table.insert(compile_lines, get_compile_name(loop_name) .. consume())
		local expressions_line = current_token.line
		local expressions = list(expression)
		local num_expressions = #expressions
		if num_expressions ~= 2 and num_expressions ~= 3 then
			throw("invalid numeric for, expected 2-3 expressions, got " .. tostring(num_expressions), expressions_line)
		end
		table.insert(compile_lines, weave(expressions))
	else
		local names = {}
		for _, var in ipairs(list(variable)) do
			add_block_declaration(var, "local", block_depth + 1)
			if type(var) == "string" then
				table.insert(names, get_compile_name(var))
			else
				table.insert(names, var.compile_name)
				table.insert(
					pre_body_compile_lines,
					"local " .. table.concat(table.map(var.declaration_names, get_compile_name), ",")
				)
				table.insert(pre_body_compile_lines, var.compile_lines)
			end
		end
		table.insert(compile_lines, weave(names))
		table.insert(compile_lines, expect("in", true))
		table.insert(compile_lines, weave(list(expression)))
	end
	table.insert(compile_lines, "do")
	table.insert(compile_lines, pre_body_compile_lines)
	table.insert(compile_lines, surround("{", "}", loop_block))
	table.insert(compile_lines, "end")
	return compile_lines
end
local function repeat_until()
	return {
		consume(),
		surround("{", "}", loop_block),
		expect("until", true),
		expression(),
	}
end
local function while_loop()
	return {
		consume(),
		expression(),
		"do",
		surround("{", "}", loop_block),
		"end",
	}
end
local function goto_jump()
	if lua_target == "5.1" or lua_target == "5.1+" then
		throw("'goto' statements only compatibly with lua targets 5.2+, jit")
	end
	consume()
	local label_line, label = current_token.line, name()
	table.insert(goto_jumps, {
		label = label,
		line = label_line,
	})
	return "goto " .. get_compile_name(label)
end
local function goto_label()
	if lua_target == "5.1" or lua_target == "5.1+" then
		throw("'goto' statements only compatibly with lua targets 5.2+, jit")
	end
	consume()
	local label = name()
	goto_labels[label] = true
	return "::" .. get_compile_name(label) .. expect("::", true)
end
local function if_else()
	local compile_lines = {}
	table.insert(compile_lines, consume())
	table.insert(compile_lines, expression())
	table.insert(compile_lines, "then")
	table.insert(compile_lines, surround("{", "}", block))
	while current_token.value == "elseif" do
		table.insert(compile_lines, consume())
		table.insert(compile_lines, expression())
		table.insert(compile_lines, "then")
		table.insert(compile_lines, surround("{", "}", block))
	end
	if current_token.value == "else" then
		table.insert(compile_lines, consume())
		if current_token.value == "if" then
			throw("unexpected tokens 'else if', did you mean 'elseif'?")
		end
		table.insert(compile_lines, surround("{", "}", block))
	end
	table.insert(compile_lines, "end")
	return compile_lines
end
local function assignment_index_chain()
	if current_token.value == "(" then
		return index_chain({
			base_compile_lines = {
				current_token.line,
				"(",
				surround("(", ")", expression),
				")",
			},
			require_chain = true,
		})
	else
		local base_name_line, base_name = current_token.line, name()
		return index_chain({
			base_compile_lines = {
				base_name_line,
				get_compile_name(base_name, block_declarations[base_name]),
			},
			has_trivial_base = true,
		})
	end
end
local function non_operator_assignment(ids, expressions)
	local assignment_ids = {}
	local assignment_block_compile_names = {}
	local assignment_block_compile_lines = {}
	for _, id in ipairs(ids) do
		if not id.needs_block_compile then
			table.insert(assignment_ids, id.compile_lines)
		else
			local assignment_name = new_tmp_name()
			table.insert(assignment_ids, assignment_name)
			table.insert(assignment_block_compile_names, assignment_name)
			table.insert(assignment_block_compile_lines, id.block_compile_lines)
			table.insert(assignment_block_compile_lines, id.compile_lines)
			table.insert(assignment_block_compile_lines, "=" .. assignment_name)
		end
	end
	local compile_lines = {}
	if #assignment_block_compile_names > 0 then
		table.insert(compile_lines, "local")
		table.insert(compile_lines, weave(assignment_block_compile_names))
	end
	table.insert(compile_lines, weave(assignment_ids))
	table.insert(compile_lines, "=")
	table.insert(compile_lines, weave(expressions))
	table.insert(compile_lines, assignment_block_compile_lines)
	return compile_lines
end
local function single_operator_assignment(id, expr, op_token, op_line)
	local compile_lines = {}
	local id_compile_lines = id.compile_lines
	if id.needs_block_compile then
		table.insert(compile_lines, id.block_compile_lines)
	end
	if not id.has_trivial_base or id.chain_len > 1 then
		local final_base_name = new_tmp_name()
		table.insert(compile_lines, "local " .. tostring(final_base_name) .. " =")
		table.insert(compile_lines, id.final_base_compile_lines)
		id_compile_lines = {
			final_base_name,
			id.final_index_compile_lines,
		}
	end
	table.insert(compile_lines, id_compile_lines)
	table.insert(compile_lines, "=")
	if type(expr) == "table" then
		expr = {
			"(",
			expr,
			")",
		}
	end
	table.insert(compile_lines, compile_binop(op_token, op_line, id_compile_lines, expr))
	return compile_lines
end
local function operator_assignment(ids, expressions, op_token, op_line)
	if #ids == 1 then
		return single_operator_assignment(ids[1], expressions[1], op_token, op_line)
	end
	local assignment_names = {}
	local assignment_compile_lines = {}
	for _, id in ipairs(ids) do
		local assignment_name = new_tmp_name()
		table.insert(assignment_names, assignment_name)
		table.insert(assignment_compile_lines, single_operator_assignment(id, assignment_name, op_token, op_line))
	end
	return {
		"local " .. tostring(table.concat(assignment_names, ",")) .. " =",
		weave(expressions),
		assignment_compile_lines,
	}
end
local function variable_assignment(first_id)
	local ids = {
		first_id,
	}
	while branch(",") do
		local id_line, id = current_token.line, assignment_index_chain()
		if id.is_function_call then
			throw("cannot assign value to function call", id_line)
		end
		table.insert(ids, id)
	end
	local op_line, op_token = current_token.line, BINOP_ASSIGNMENT_TOKENS[current_token.value] and consume()
	if BITOPS[op_token] and (lua_target == "5.1+" or lua_target == "5.2+") and not bitexpr then
		throw("must specify bitexpr or bitlib for compiling bit operations when targeting 5.1+ or 5.2+", op_line)
	end
	expect("=", true)
	local expressions = list(expression)
	if op_token then
		return operator_assignment(ids, expressions, op_token, op_line)
	else
		return non_operator_assignment(ids, expressions)
	end
end
local function variable_declaration(scope)
	local assignment_names = {}
	local has_destructure = false
	local destructure_declaration_names = {}
	local destructure_compile_lines = {}
	for _, var in
		ipairs(list(function()
			return variable(scope)
		end))
	do
		add_block_declaration(var, scope)
		if type(var) == "string" then
			table.insert(assignment_names, get_compile_name(var, scope))
		else
			has_destructure = true
			table.insert(assignment_names, var.compile_name)
			table.insert(destructure_compile_lines, var.compile_lines)
			if scope == "local" then
				table.merge(destructure_declaration_names, table.map(var.declaration_names, get_compile_name))
			else
				table.insert(destructure_declaration_names, var.compile_name)
			end
		end
	end
	if has_destructure then
		expect("=", true)
	elseif scope == "local" and current_token.value ~= "=" then
		return "local " .. table.concat(assignment_names, ",")
	elseif not branch("=") then
		return ""
	end
	local compile_lines = {}
	if has_destructure then
		table.insert(compile_lines, "local " .. table.concat(destructure_declaration_names, ","))
	end
	if scope == "local" then
		table.insert(compile_lines, "local")
	end
	table.insert(compile_lines, table.concat(assignment_names, ",") .. "=")
	table.insert(compile_lines, weave(list(expression)))
	table.insert(compile_lines, destructure_compile_lines)
	return compile_lines
end
function statement()
	local compile_lines = {}
	if current_token.value == "break" then
		table.insert(compile_lines, loop_break())
	elseif current_token.value == "continue" then
		table.insert(compile_lines, loop_continue())
	elseif current_token.value == "goto" then
		table.insert(compile_lines, goto_jump())
	elseif current_token.value == "::" then
		table.insert(compile_lines, goto_label())
	elseif current_token.value == "do" then
		table.insert(compile_lines, do_block())
	elseif current_token.value == "if" then
		table.insert(compile_lines, if_else())
	elseif current_token.value == "for" then
		table.insert(compile_lines, for_loop())
	elseif current_token.value == "while" then
		table.insert(compile_lines, while_loop())
	elseif current_token.value == "repeat" then
		table.insert(compile_lines, repeat_until())
	elseif current_token.value == "return" then
		table.insert(compile_lines, block_return())
	elseif current_token.value == "function" then
		table.insert(compile_lines, function_declaration())
	elseif current_token.value == "local" or current_token.value == "global" or current_token.value == "module" then
		local scope_line, scope = current_token.line, consume()
		if scope == "module" then
			if block_depth > 1 then
				throw("module declarations must appear at the top level", scope_line)
			end
			has_module_declarations = true
		end
		if current_token.value == "function" then
			table.insert(compile_lines, function_declaration(scope))
		else
			table.insert(compile_lines, variable_declaration(scope))
		end
	else
		local chain = assignment_index_chain()
		if not chain.is_function_call then
			table.insert(compile_lines, variable_assignment(chain))
		elseif chain.needs_block_compile then
			table.insert(compile_lines, "do")
			table.insert(compile_lines, chain.block_compile_lines)
			table.insert(compile_lines, chain.compile_lines)
			table.insert(compile_lines, "end")
		else
			table.insert(compile_lines, chain.compile_lines)
		end
	end
	if current_token.value == ";" then
		table.insert(compile_lines, consume())
	elseif current_token.value == "(" then
		table.insert(compile_lines, ";")
	end
	return compile_lines
end
local function module_block()
	local compile_lines = {}
	block_declarations = {}
	block_declaration_stack[block_depth] = block_declarations
	if current_token.type == TOKEN_TYPES.SHEBANG then
		table.insert(compile_lines, consume())
	end
	while current_token.type ~= TOKEN_TYPES.EOF do
		table.insert(compile_lines, statement())
	end
	if has_module_declarations then
		if module_return_line ~= nil then
			throw("cannot use 'return' w/ 'module' declarations", module_return_line)
		end
		table.insert(compile_lines, 1, "local _MODULE = {}")
		table.insert(compile_lines, "return _MODULE")
	end
	return compile_lines
end
local function collect_compile_lines(lines, state)
	for _, line in ipairs(lines) do
		if type(line) == "number" then
			state.source_line = line
		elseif type(line) == "string" then
			table.insert(state.compile_lines, line)
			table.insert(state.source_map, state.source_line)
		else
			collect_compile_lines(line, state)
		end
	end
end
return function(source, options)
	if options == nil then
		options = {}
	end
	tokens = tokenize(source, options.alias)
	current_token_index = 1
	current_token = tokens[current_token_index]
	block_depth = 1
	tmp_name_counter = 1
	break_name = nil
	has_continue = false
	has_module_declarations = false
	is_module_return_block = true
	module_return_line = nil
	is_varargs_block = true
	block_declarations = {}
	block_declaration_stack = {}
	goto_jumps = {}
	goto_labels = {}
	alias = options.alias or get_source_alias(source)
	lua_target = options.lua_target or config.lua_target
	if options.bitlib then
		print("WARNING: `bitlib` has been deprecated in favor of `bitexpr`.")
	end
	local bitlib = options.bitlib or config.bitlib
	bitexpr = options.bitexpr
		or config.bitexpr
		or (bitlib and "require('" .. tostring(bitlib) .. "')")
		or (lua_target == "5.1" and "require('bit')")
		or (lua_target == "jit" and "bit")
		or (lua_target == "5.2" and "bit32")
	local source_map = {}
	local compile_lines = {}
	collect_compile_lines(module_block(), {
		compile_lines = compile_lines,
		source_map = source_map,
		source_line = current_token.line,
	})
	for _, __ERDE_TMP_1936__ in ipairs(goto_jumps) do
		local label, line
		label = __ERDE_TMP_1936__.label
		line = __ERDE_TMP_1936__.line
		if goto_labels[label] == nil then
			throw("failed to find goto label '" .. tostring(label) .. "'", line)
		end
	end
	table.insert(
		compile_lines,
		"-- Compiled with Erde " .. tostring(VERSION) .. " w/ Lua target " .. tostring(lua_target)
	)
	table.insert(compile_lines, COMPILED_FOOTER_COMMENT)
	return table.concat(compile_lines, "\n"), source_map
end
-- Compiled with Erde 1.0.0-1 w/ Lua target 5.1+
-- __ERDE_COMPILED__
