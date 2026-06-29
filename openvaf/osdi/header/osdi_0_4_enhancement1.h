#pragma once

#ifndef NO_STD
#include <stdint.h>
#endif

/* Companion to osdi_0_4.h — assumes OSDI_NUM_DESCRIPTORS / OsdiDescriptor from
 * that header are in scope on the consumer side. */

/*
 * OSDI 0.4 — Enhancement 1:  absdelay() support
 * =============================================
 *
 * This header documents an ADDITIVE, backward-compatible extension to the
 * OSDI 0.4 ABI (see osdi_0_4.h).  It is emitted by OpenVAF-reloaded (version2)
 * and consumed by ngspice-46 (version2) to implement the Verilog-A
 * `absdelay()` operator.
 *
 * Nothing in osdi_0_4.h changes:
 *   - The `OsdiDescriptor` struct layout is UNCHANGED (OSDI_DESCRIPTOR_SIZE and
 *     binary compatibility are preserved).
 *   - This extension adds ONE new struct type (OsdiAbsDelayInfo) and TWO new
 *     optional global symbols (OSDI_ABSDELAY_COUNTS, OSDI_ABSDELAY_INFOS).
 *
 * A simulator that does not know about this extension simply ignores the two
 * symbols; a model that uses no `absdelay()` does not export them at all.
 * Therefore old simulators run new models (minus absdelay) and new simulators
 * run old models unchanged.
 *
 *
 * 1. Model of `absdelay()`
 * ------------------------
 * `absdelay(y_expr, td [, tdmax])` is lowered to TWO synthetic implicit-node
 * equations per call ("delay slot"):
 *
 *     eq_y  (input node  y_synth):  V(y_synth) = y_expr
 *                                   -> the MODEL stamps this row (a normal
 *                                      resistive residual emitted by OpenVAF).
 *
 *     eq_z  (output node z):        V(z) = delayed( V(y_synth), td )
 *                                   -> the SIMULATOR stamps this row using a
 *                                      waveform history of V(y_synth):
 *                                        DC   : V(z) = V(y_synth)         (wire)
 *                                        TRAN : V(z) = interp(history, t-td)
 *                                        AC   : V(z) = e^{-j*omega*td} * V(y_synth)
 *
 * The value of the `absdelay()` expression in the model body is V(z).  The
 * model leaves eq_z's matrix row empty (zero contribution); the simulator must
 * fill it.  If `tdmax` is given the effective delay is min(td, tdmax); `td` is
 * recomputed every evaluation and written into instance data (see td_offset).
 *
 *
 * 2. Per-slot descriptor
 * ----------------------
 * One OsdiAbsDelayInfo describes one delay slot.  It is 12 bytes:
 * three uint32_t fields, no padding.
 */
typedef struct OsdiAbsDelayInfo {
  uint32_t y_node;     /* OSDI node index of the synthetic input node y_synth.
                        * Index into the descriptor's node table / the per-
                        * instance node_mapping (same space as
                        * OsdiJacobianEntry.nodes and OsdiNode).            */
  uint32_t z_node;     /* OSDI node index of the delay output node z.       */
  uint32_t td_offset;  /* Byte offset, within the per-instance OSDI data
                        * block, of the `double td` value for this slot
                        * (the effective, post-tdmax delay in seconds).
                        * The simulator reads *(double*)((char*)inst +
                        * node_mapping/instance base + td_offset).          */
} OsdiAbsDelayInfo;


/*
 * 3. Global symbols (exported from the .osdi object, optional)
 * -----------------------------------------------------------
 * Present ONLY when at least one module in the object uses absdelay().
 *
 *   const uint32_t OSDI_ABSDELAY_COUNTS[OSDI_NUM_DESCRIPTORS];
 *       OSDI_ABSDELAY_COUNTS[i] = number of delay slots in descriptor i
 *       (0 if descriptor i uses no absdelay).  Same indexing as
 *       OSDI_DESCRIPTORS.
 *
 *   const OsdiAbsDelayInfo OSDI_ABSDELAY_INFOS[ sum(OSDI_ABSDELAY_COUNTS) ];
 *       All slots for all descriptors, concatenated in descriptor order.
 *       Descriptor i's slots are the OSDI_ABSDELAY_COUNTS[i] entries starting
 *       at offset  sum(OSDI_ABSDELAY_COUNTS[0..i]).
 *
 * Loader sketch (consumer side):
 *
 *   const uint32_t        *counts = dlsym(h, "OSDI_ABSDELAY_COUNTS"); // may be NULL
 *   const OsdiAbsDelayInfo *infos = dlsym(h, "OSDI_ABSDELAY_INFOS");  // may be NULL
 *   uint32_t off = 0;
 *   for (uint32_t i = 0; i < OSDI_NUM_DESCRIPTORS; i++) {
 *       uint32_t n = counts ? counts[i] : 0;
 *       const OsdiAbsDelayInfo *slots = (n && infos) ? &infos[off] : NULL;
 *       off += n;
 *       // store (n, slots) for descriptor i
 *   }
 *
 *
 * 4. What the simulator must do for each slot k of an instance
 * ------------------------------------------------------------
 *   setup : create two matrix entries on the z row:
 *               J[z_node, y_node]  and  J[z_node, z_node]
 *           and allocate a per-slot waveform history of V(y_synth).
 *   DC / OP : J[z,y] += 1 ; J[z,z] += -1            (V(z) = V(y_synth))
 *   TRAN    : look up V(y_synth) at (t - td) from history, stamp the linear
 *             interpolation into the z row; commit the converged V(y_synth)
 *             into history at each accepted timepoint.  Delays below ~1e-15 s
 *             should be treated as DC pass-through to avoid collapsing the
 *             time step.
 *   AC      : J[z,y] += cos(omega*td) - j*sin(omega*td) ;  J[z,z] += -1
 *
 * The reference consumer implementation lives in ngspice-46/src/osdi:
 *   osdiregistry.c (read symbols), osdisetup.c (allocate + KLU bind),
 *   osdiload.c (DC/TRAN stamp), osdiaccept.c (history commit),
 *   osdiacld.c (AC stamp).  The matching emitter is OpenVAF
 *   openvaf/osdi/src/lib.rs (export) + inst_data.rs (td storage).
 */
