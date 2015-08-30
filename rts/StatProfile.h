/* ---------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2014-2015
 *
 * A simple statistical profiler
 *
 * --------------------------------------------------------------------------*/


void statprof_init(void);

/* The profiler can trigger a sample based on a variety of conditions.
   These are those conditions. */
enum sample_reason {
  STATPROF_SAMPLE_TIME = 0x0,    /* Sample due to timer */
  STATPROF_SAMPLE_HEAP,          /* Sample due to heap allocations */
  STATPROF_SAMPLE_BLACKHOLE,     /* Sample due to a black hole block */
};

void statprof_sample(enum sample_reason reason);
