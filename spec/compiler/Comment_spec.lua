local erde = require('erde')

describe('Comment', function()
  spec('single line comment', function()
    assert.are.equal('', erde.compile('-- test'))
  end)
  spec('multi line comment', function()
    assert.are.equal('', erde.compile([[
    ---
    -- This is a
    -- multiline comment
    ---
    ]]))
  end)
end)
