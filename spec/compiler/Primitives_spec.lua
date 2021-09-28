local erde = require('erde')

spec('numbers', function()
  assert.are.equal(1, erde.eval('return 1'))
  assert.are.equal(163, erde.eval('return 0xA3'))
  assert.are.equal(163, erde.eval('return 0xa3'))
  assert.are.equal(.2, erde.eval('return .2'))
  assert.are.equal(9.2, erde.eval('return 9.2'))
  assert.are.equal(1000, erde.eval('return 1e3'))
  assert.are.equal(1000, erde.eval('return 1E3'))
  assert.are.equal(1000, erde.eval('return 1e+3'))
  assert.are.equal(1000, erde.eval('return 1E+3'))
  assert.are.equal(.001, erde.eval('return 1e-3'))
  assert.are.equal(.001, erde.eval('return 1E-3'))
end)

spec('short strings', function()
  assert.are.equal('hello world', erde.eval('return "hello world"'))
  assert.are.equal('hello world', erde.eval("return 'hello world'"))
  assert.are.equal('hello\nworld', erde.eval('return "hello\\nworld"'))
end)

spec('long strings', function()
  assert.are.equal('hello world', erde.eval('return `hello world`'))
  assert.are.equal('hello { world }', erde.eval('return `hello \\{ world \\}`'))
  assert.are.equal('hello ` world `', erde.eval('return `hello \\` world \\``'))
  assert.are.equal('hello world', erde.eval([[
    local msg = 'world'
    return `hello {msg}`
  ]]))
end)
