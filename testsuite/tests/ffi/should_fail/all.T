
# Missing:
# test('cc002', normal, compile_fail, [''])

test('ccfail001', normal, compile_fail, [''])
test('ccfail002', normal, compile_fail, [''])
test('ccfail003', normal, compile_fail, [''])
test('T3066', normal, compile_fail, [''])
test('ccfail004', [extra_files(['Ccfail004A.hs'])], multimod_compile_fail, ['ccfail004', '-v0'])
test('ccfail005', normal, compile_fail, [''])
test('ccall_value', normal, compile_fail, [''])
test('capi_value_function', normal, compile_fail, [''])
test('T5664', normal, compile_fail, ['-v0'])
test('T7506', normal, compile_fail, [''])
test('T7243', normal, compile_fail, [''])
test('T10461', normal, compile_fail, [''])

# UnsafeReenter seems to just hang instead of erroring out
# with the threaded1, threaded2 and profthreaded ways,
# see #14912.
test('UnsafeReenter',
     [omit_ways(threaded_ways), exit_code(1)],
     compile_and_run,
     ['UnsafeReenterC.c'])
