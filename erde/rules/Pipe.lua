local utils = require('erde.utils')

-- -----------------------------------------------------------------------------
-- Pipe
-- -----------------------------------------------------------------------------

local Pipe = { ruleName = 'Pipe' }

-- -----------------------------------------------------------------------------
-- Parse
-- -----------------------------------------------------------------------------

function Pipe.parse(ctx, opts)
  local node = { initValues = opts.initValues }
  ctx:assert('>>', true)

  while ctx:branch('>>') do
    node[#node + 1] = ctx:FunctionCall()
  end

  return node
end

-- -----------------------------------------------------------------------------
-- Compile
-- -----------------------------------------------------------------------------

function Pipe.compile(ctx, node)
  local compiled = {}

  local initValues = {}
  for i, initValue in ipairs(node.initValues) do
    initValues[#initValues + 1] = ctx:compile(initValue)
  end

  local pipeArgs = table.concat(initValues, ',')
  local pipeResult = ctx:newTmpName()
  compiled[#compiled + 1] = ('local %s = { %s }'):format(pipeResult, pipeArgs)

  for i, pipe in ipairs(node) do
    pipeArgs = pipeResult
    pipeResult = ctx:newTmpName()

    local pipeArgsLen = ctx:newTmpName()
    compiled[#compiled + 1] = ('local %s = #%s'):format(pipeArgsLen, pipeArgs)

    for i, expr in ipairs(pipe[#pipe].value) do
      compiled[#compiled + 1] = ('%s[%s + %s] = %s'):format(
        pipeArgs,
        pipeArgsLen,
        i,
        ctx:compile(expr)
      )
    end

    local pipeCopy = utils.shallowCopy(pipe) -- Do not mutate AST
    table.remove(pipeCopy)

    compiled[#compiled + 1] = ('local %s = { %s(%s(%s)) }'):format(
      pipeResult,
      ctx:compile(pipeCopy),
      'unpack',
      pipeArgs
    )
  end

  return table.concat({
    '(function()',
    table.concat(compiled, '\n'),
    ('return %s(%s)'):format('unpack', pipeResult),
    'end)()',
  }, '\n')
end

-- -----------------------------------------------------------------------------
-- Return
-- -----------------------------------------------------------------------------

return Pipe
