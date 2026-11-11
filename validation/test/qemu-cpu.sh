# QEMU CPU model for the differential tests (sourced by test/run.sh and test/sys/run.sh).
# An EPYC-Rome (Zen 2) CPU under TCG, minus the features TCG does not implement and warns about
# (QEMU 11.1: FFXSR, LM (qemu-system-i386 has no long mode), MisalignSse, OSVW, TopoExt,
# PerfCtrExtCore, CLZERO, IBPB, STIBP, NRIPS, XSAVEC, XSAVES). QEMU therefore executes Zen 2
# instructions (SSE3..SSE4.2, SSE4a, AES, SHA, AVX, AVX2, FMA, F16C, BMI, ...) that the model may not
# implement yet; generators skip those forms (test/isa_forms.py, NOT_YET_IMPLEMENTED).
QEMU_CPU=${QEMU_CPU:-EPYC-Rome,-fxsr-opt,-lm,-misalignsse,-osvw,-topoext,-perfctr-core,-clzero,-ibpb,-amd-stibp,-nrip-save,-xsavec,-xsaves}
