-- -----------------------------------------------------------------------------
-- Dot Index
-- -----------------------------------------------------------------------------

spec('dot index #5.1+', function()
  assert_eval(1, '({ a = 1 }).a')

  assert_run(2, [[
    local a = { b = 2 }
    return a.b
  ]])

  assert_run(3, [[
    local a = { end = 3 }
    return a.end
  ]])
end)

spec('dot index source map #5.1+', function()
  assert_source_map(1, [[
    math.round(a.b)
  ]])

  assert_source_map(2, [[
    math.round(a
    .b)
  ]])
end)

-- -----------------------------------------------------------------------------
-- Bracket Index
-- -----------------------------------------------------------------------------

spec('bracket index #5.1+', function()
  assert_eval(1, '({ 1 })[1]')

  assert_run(2, [[
    local a = { [5] = 2 }
    return a[2 + 3]
  ]])

  assert_run(3, [[
    local a = { end = 3 }
    local key = 'end'
    return a[key]
  ]])
end)

spec('bracket index source map #5.1+', function()
  assert_source_map(1, [[
    math.round(a['b'])
  ]])

  assert_source_map(2, [[
    math.round(a
    ['b'])
  ]])
end)

-- -----------------------------------------------------------------------------
-- Method Call
-- -----------------------------------------------------------------------------

spec('method call #5.1+', function()
  assert_run(1, [[
    local a = { b = c => c + self.d, d = 2 }
    return a:b(-1)
  ]])

  assert_run(2, [[
    local a = { end = () => 2 }
    return a:end()
  ]])

  assert_eval(3, '({ end = () => 3 }):end()')

  assert.has_error(function()
    compile('a:b')
  end)
end)

describe('method call source map', function()
  spec('#5.1+', function()
    assert_source_map(1, [[
      math.round(a:b())
    ]])

    assert_source_map(2, [[
      math.round(a
      :b())
    ]])
  end)

  spec('#5.1 jit #5.4', function()
    assert_source_map(3, [[
      local a = {}
      a
      :b(4)
    ]])

    assert_source_map(4, [[

      local a = 'a'
      a
      :gsub(4)
    ]])
  end)

  spec('#5.2 #5.3', function()
    assert_source_map(2, [[
      local a = {}
      a
      :b(4)
    ]])

    assert_source_map(3, [[

      local a = 'a'
      a
      :gsub(4)
    ]])
  end)
end)

-- -----------------------------------------------------------------------------
-- Function Call
-- -----------------------------------------------------------------------------

spec('function call #5.1+', function()
  assert_run(1, [[
    local a = () -> 1
    return a()
  ]])

  assert_run(2, [[
    local a = b -> b + 1
    return a(1)
  ]])

  assert_run(3, [[
    local a = { b = () -> 3 }
    return a.b()
  ]])
end)

-- -----------------------------------------------------------------------------
-- Misc
-- -----------------------------------------------------------------------------

spec('nested parens base #5.1+', function()
  assert_eval(1, '((({ a = 1 }))).a')
end)

spec('chain #5.1+', function()
  assert_run(1, [[
    local a = { b = { 1 } }
    return a.b[1]
  ]])

  assert_run(2, [[
    local a = { { b = 2 } }
    return a[1].b
  ]])
end)

spec('string base #5.1+', function()
  assert_eval('bbb', '"aaa":gsub("a", "b")')
  assert_eval('bbb', "'aaa':gsub('a', 'b')")
  assert_eval('bbb', "[[aaa]]:gsub('a', 'b')")
end)

spec('index chain base source map #5.1+', function()
  assert_source_map(1, [[
    (nil)()
  ]])

  assert_source_map(2, [[

    my_fake_function()
  ]])

  assert_source_map(3, [[

    local a =
    my_fake_function()
  ]])

  assert_source_map(4, [[


    local a =
    (nil)()
  ]])
end)
