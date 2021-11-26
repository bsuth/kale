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
  local node = {
    idList = ctx:List({ rule = ctx.Id }),
    op = ctx:Binop(),
  }

  if node.op then
    if BINOP_ASSIGNMENT_BLACKLIST[node.op.token] then
      ctx:throwError('Cannot use operator assignment w/ ' .. node.op.token)
    elseif #node.idList > 1 then
      ctx:throwError(
        'Cannot use assignment operations w/ more than 1 assignment'
      )
    else
      ctx:consume(#node.op.token)
    end
  end

  if not ctx:branchChar('=') then
    ctx:throwExpected('=')
  end

  node.exprList = ctx:List({ rule = ctx.Expr })
  return node
end

-- -----------------------------------------------------------------------------
-- Compile
-- -----------------------------------------------------------------------------

function Assignment.compile(ctx, node)
  local idList = {}
  for i, id in ipairs(node.idList) do
    idList[#idList + 1] = ctx:compile(id)
  end

  local exprList = {}
  for i, expr in ipairs(node.exprList) do
    exprList[#exprList + 1] = ctx:compile(expr)
  end

  if node.op then
    return idList[1]
      .. ' = '
      .. ctx.compileBinop(node.op, idList[1], exprList[1])
  else
    return table.concat(idList, ',') .. ' = ' .. table.concat(exprList, ',')
  end
end

-- -----------------------------------------------------------------------------
-- Return
-- -----------------------------------------------------------------------------

return Assignment
