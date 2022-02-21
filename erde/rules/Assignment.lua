local C = require('erde.constants')

-- These operators cannot be used w/ operator assignment
local BINOP_ASSIGNMENT_BLACKLIST = {
  ['?'] = true,
  ['=='] = true,
  ['~='] = true,
  ['<='] = true,
  ['>='] = true,
  ['<'] = true,
  ['>'] = true,
}

-- -----------------------------------------------------------------------------
-- Assignment
-- -----------------------------------------------------------------------------

local Assignment = { ruleName = 'Assignment' }

-- -----------------------------------------------------------------------------
-- Parse
-- -----------------------------------------------------------------------------

function Assignment.parse(ctx)
  local node = { id = ctx:Id() }

  if BINOP_ASSIGNMENT_BLACKLIST[ctx.token] then
    error('Invalid assignment operator: ' .. ctx.token)
  elseif C.BINOPS[ctx.token] then
    node.op = C.BINOPS[ctx:consume()]
  end

  ctx:assert('=')
  node.expr = ctx:Expr()
  return node
end

-- -----------------------------------------------------------------------------
-- Compile
-- -----------------------------------------------------------------------------

function Assignment.compile(ctx, node)
  local optChain = node.id.ruleName == 'OptChain'
    and ctx:compileOptChain(node.id)

  local compiledId = optChain and optChain.chain or ctx:compile(node.id)
  local compiledExpr = ctx:compile(node.expr)

  local compiledAssignment
  if node.op then
    compiledAssignment = compiledId
      .. ' = '
      .. ctx:compileBinop(node.op, compiledId, compiledExpr)
  else
    compiledAssignment = compiledId .. ' = ' .. compiledExpr
  end

  if not optChain or #optChain.optSubChains == 0 then
    return compiledAssignment
  else
    local optChecks = {}
    for i, optSubChain in ipairs(optChain.optSubChains) do
      table.insert(optChecks, optSubChain .. ' ~= nil')
    end

    return ('if %s then\n%s\nend'):format(
      table.concat(optChecks, ' and '),
      compiledAssignment
    )
  end
end

-- -----------------------------------------------------------------------------
-- Return
-- -----------------------------------------------------------------------------

return Assignment
