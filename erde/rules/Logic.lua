local _ = require('erde.rules.helpers')
local supertable = require('erde.supertable')

return {
  BraceBlock = {
    pattern = _.Pad('{') * _.CsV('Block') * _.Pad('}'),
  },
  IfElse = {
    pattern = _.Product({
      _.Product({
        _.Cc(1),
        _.Pad('if'),
        _.CsV('Expr'),
        _.V('BraceBlock'),
      }) / _.map('variant', 'expr', 'block'),
      (_.Product({
        _.Cc(2),
        _.Pad('elseif'),
        _.CsV('Expr'),
        _.V('BraceBlock'),
      }) / _.map('variant', 'expr', 'block')) ^ 0,
      (_.Product({
        _.Cc(3),
        _.Pad('else'),
        _.V('BraceBlock'),
      }) / _.map('variant', 'block')) ^ -1,
    }) / _.pack,
    compiler = function(conditionals)
      return conditionals:map(function(cond)
        if cond.variant == 1 then
          return 'if '..cond.expr..' then '..cond.block
        elseif cond.variant == 2 then
          return 'elseif '..cond.expr..' then '..cond.block
        elseif cond.variant == 3 then
          return 'else '..cond.block
        end
      end):push('end'):join(' ')
    end,
  },
  NumericFor = {
    pattern = _.Product({
      _.Pad('for'),
      _.CsV('Name'),
      _.Pad('='),
      _.List(_.CsV('Expr'), {
        minlen = 2,
        maxlen = 3,
        trailing = false,
      }),
      _.V('BraceBlock'),
    }),
    compiler = function(name, exprlist, block)
      return ('for %s = %s do %s end'):format(name, exprlist:join(','), block)
    end,
  },
  GenericFor = {
    pattern = _.Product({
      _.Pad('for'),
      _.CsV('Name'),
      _.Pad(','),
      _.CsV('Name'),
      _.Pad('in'),
      _.CsV('Expr'),
      _.V('BraceBlock'),
    }),
    compiler = function(keyname, valuename, iterator, block)
      return ('for %s,%s in %s do %s end'):format(
        keyname,
        valuename,
        iterator,
        block
      )
    end,
  },
  WhileLoop = {
    pattern = _.Product({
      _.Pad('while'),
      _.CsV('Expr'),
      _.V('BraceBlock'),
    }),
    compiler = _.template('while %1 do %2 end'),
  },
  RepeatUntil = {
    pattern = _.Product({
      _.Pad('repeat'),
      _.V('BraceBlock'),
      _.Pad('until'),
      _.Parens(_.CsV('Expr')),
    }),
    compiler = _.template('repeat %1 until (%2)'),
  },
  DoBlock = {
    pattern = _.Product({
      _.Pad('do'),
      _.V('BraceBlock'),
    }),
    compiler = function(block)
      -- This is pretty crude, but generally covers most cases at VERY little
      -- compile cost. If at some point in the future we want to REALLY optimize
      -- the generated lua code (which will cause performance drops in the
      -- compiler) then this should be changed.
      return block:find('return')
        and '(function() '..block..' end)()'
        or 'do '..block..' end'
    end,
  },
}
