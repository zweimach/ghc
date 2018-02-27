/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team 1998-2008
 *
 * General utilities for walking the heap
 *
 * ---------------------------------------------------------------------------*/

#pragma once

typedef void (walk_closures_cb)(StgClosure **, void *);

/*
 * Walk over all of the pointers referenced by a StgLargeSRT.
 */
INLINE_HEADER void
walk_large_srt(walk_closures_cb *cb, StgLargeSRT *large_srt, void *user)
{
    const uint32_t size = (uint32_t)large_srt->l.size;
    StgClosure **p = (StgClosure **)large_srt->srt;
    uint32_t i;

    for (i = 0; i < size / BITS_IN(W_); i++) {
        StgWord bitmap = large_srt->l.bitmap[i];
        // skip zero words: bitmaps can be very sparse, and this helps
        // performance a lot in some cases.
        if (bitmap != 0) {
            for (uint32_t j = 0; j < BITS_IN(W_); j++) {
                if ((bitmap & 1) != 0) {
                    cb(p, user);
                }
                p++;
                bitmap = bitmap >> 1;
            }
        } else {
            p += BITS_IN(W_);
        }
    }
    if (size % BITS_IN(W_) != 0) {
        StgWord bitmap = large_srt->l.bitmap[i];
        for (uint32_t j = 0; j < size % BITS_IN(W_); j++) {
            if ((bitmap & 1) != 0) {
                cb(p, user);
            }
            p++;
            bitmap = bitmap >> 1;
        }
    }

}

INLINE_HEADER void
walk_large_bitmap(walk_closures_cb *cb,
                  StgClosure **p,
                  StgLargeBitmap *large_bitmap,
                  StgWord size,
                  void *user)
{
    uint32_t b = 0;

    for (uint32_t i = 0; i < size; b++) {
        StgWord bitmap = large_bitmap->bitmap[b];
        uint32_t j = stg_min(size-i, BITS_IN(W_));
        i += j;
        for (; j > 0; j--, p++) {
            if ((bitmap & 1) == 0) {
                cb(p, user);
            }
            bitmap = bitmap >> 1;
        }
    }
}
