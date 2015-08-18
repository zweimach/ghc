/* ---------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2015-2015
 *
 * Codemap, map from instruction pointers to function names
 *
 * --------------------------------------------------------------------------*/

#ifndef PRIVATE_CODEMAP_H
#define PRIVATE_CODEMAP_H

// To be called once when the RTS starts. This is a very fast and will always
// be done once during the life-time of a Haskell program.
void initCodemap(void);

#endif // PRIVATE_CODEMAP_H
