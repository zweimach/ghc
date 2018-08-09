test('seward-space-leak',
     [extra_files(['Main.lhs']),
      when(fast(), skip),
      expect_broken_for(welltyped_gc_bug(73), ['nonmoving', 'nonmoving_thr'])],
     multimod_compile_and_run,
     ['Main', ''])
