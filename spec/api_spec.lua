local erde = require('erde')
local config = require('erde.config')
local lib = require('erde.lib')

-- -----------------------------------------------------------------------------
-- Helpers
-- -----------------------------------------------------------------------------

function make_load_spec(callback)
  return function()
    local old_lua_target = config.lua_target
    callback()
    config.lua_target = old_lua_target
  end
end

-- -----------------------------------------------------------------------------
-- API
-- -----------------------------------------------------------------------------

spec('api errors #5.1+', function()
  -- There is a separate spec for error rewriting. Here we simply ensure that
  -- they are available via the API.
  assert.are.equal(erde.rewrite, lib.rewrite)
  assert.are.equal(erde.traceback, lib.traceback)
end)

describe('api compile #5.1+', function()
  spec('can compile', function()
    assert.has_no.errors(function()
      erde.compile('')
      erde.compile('', {})
      erde.compile('return')
      erde.compile('return', {})
    end)
  end)

  spec('can change lua target', function()
    assert.has.errors(function()
      erde.compile('goto test', { lua_target = '5.1' })
    end)
    assert.has_no.errors(function()
      erde.compile('goto test', { lua_target = 'jit' })
    end)
  end)

  spec('can change bitlib', function()
    local compiled = erde.compile('print(1 & 1)', { bitlib = 'mybitlib' })
    assert.is_not.falsy(compiled:find('mybitlib'))
  end)

  spec('can specify alias', function()
    local ok, result = pcall(function()
      erde.compile('print(', { alias = 'myalias' })
    end)

    assert.are.equal(false, ok)
    assert.are.equal('myalias:1: unexpected eof (expected expression)', result)
  end)

  spec('returns code + sourcemap', function()
    local compiled, sourcemap = erde.compile('')
    assert.are.equal(type(compiled), 'string')
    assert.are.equal(type(sourcemap), 'table')

    local compiled, sourcemap = erde.compile('print("")')
    assert.are.equal(type(compiled), 'string')
    assert.are.equal(type(sourcemap), 'table')
  end)
end)

describe('api run #5.1+', function()
  spec('can run', function()
    assert.has_no.errors(function()
      erde.run('')
      erde.run('', {})
      erde.run('return')
      erde.run('return', {})
    end)
  end)

  spec('can change bitlib', function()
    local ok, result = pcall(function()
      return erde.run('print(1 & 1)', { bitlib = 'mybitlib' })
    end)

    assert.are.equal(false, ok)
    assert.is_not.falsy(result:find("module 'mybitlib' not found"))
  end)

  spec('can specify alias', function()
    local ok, result = pcall(function()
      erde.run('print(', { alias = 'myalias' })
    end)

    assert.are.equal(false, ok)
    assert.are.equal('myalias:1: unexpected eof (expected expression)', result)

    local ok, result = xpcall(function()
      erde.run('error("myerror")', { alias = 'myalias' })
    end, erde.rewrite)

    assert.are.equal(false, ok)
    assert.are.equal('myalias:1: myerror', result)
  end)

  spec('can disable source maps', function()
    local ok, result = xpcall(function()
      erde.run('error("myerror")', {
        alias = 'myalias',
        disable_source_maps = true,
      })
    end, erde.rewrite)

    assert.are.equal(false, ok)
    assert.are.equal('myalias:(compiled:1): myerror', result)
  end)

  spec('handles multiple returns', function()
    local a, b, c = erde.run('return 1, 2, 3')
    assert.are.equal(a, 1)
    assert.are.equal(b, 2)
    assert.are.equal(c, 3)
  end)
end)

describe('api load / unload #5.1+', function()
  local searchers = package.loaders or package.searchers
  local native_num_searchers = #searchers
  local native_traceback = debug.traceback

  spec('can load', make_load_spec(function()
    erde.load()
    assert.are.equal(native_num_searchers + 1, #searchers)
  end))

  spec('can be called multiple times', make_load_spec(function()
    erde.load()
    assert.are.equal(native_num_searchers + 1, #searchers)
    erde.load()
    assert.are.equal(native_num_searchers + 1, #searchers)
  end))

  spec('has flexible args', make_load_spec(function()
    assert.has_no.errors(function()
      erde.load()
      erde.load('5.1')
      erde.load('5.1', {})
      erde.load({})
    end)
  end))

  spec('can specify Lua target', make_load_spec(function()
    erde.load('5.1')
    assert.are.equal('5.1', config.lua_target)

    assert.has.errors(function()
      erde.load('5.5') -- invalid target
    end)
  end))

  spec('can specify keep_traceback', make_load_spec(function()
    erde.load({ keep_traceback = true })
    assert.are.equal(native_traceback, debug.traceback)

    erde.load({ keep_traceback = false })
    assert.are_not.equal(native_traceback, debug.traceback)
  end))

  spec('can specify bitlib', make_load_spec(function()
    erde.load({ bitlib = 'mybitlib' })
    assert.are.equal(config.bitlib, 'mybitlib')
  end))

  spec('can specify disable_source_maps', make_load_spec(function()
    erde.load({ disable_source_maps = true })
    assert.are.equal(true, config.disable_source_maps)

    local ok, result = xpcall(function()
      erde.run('error("myerror")', { alias = 'myalias' })
    end, erde.rewrite)

    assert.are.equal(false, ok)
    assert.are.equal('myalias:(compiled:1): myerror', result)
  end))

  spec('can unload', make_load_spec(function()
    erde.load() -- reset any flags
    erde.unload()
    assert.are.equal(native_num_searchers, #searchers)
  end))
end)
