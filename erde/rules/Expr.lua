local _ = require('erde.rules.helpers')

return {
  SubExpr = {
    pattern = _.Sum({
     _.V('Function'),
     _.V('IdExpr'),
     _.V('Table'),
     _.V('String'),
     _.V('Number'),
     _.P('true'),
     _.P('false'),
     _.Pad('(') * _.V('Expr') * _.Pad(')'),
    }),
  },
  Expr = {
    pattern = _.Sum({
      _.V('Operation'),
      _.V('SubExpr'),
    }),
  },
}
