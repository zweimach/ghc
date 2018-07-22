test('heap_all',
     [when(have_profiling(),
      extra_ways(['prof'])),
      # These ways produce slightly different heap representations.
      # Currently we don't test them.
      omit_ways(['ghci', 'hpc', 'sanity', 'nonmoving', 'nonmoving_thr']),
     ],
     compile_and_run, [''])
