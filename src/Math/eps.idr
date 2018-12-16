module Math

%include C "eps.h"
%link C "eps.o"

machineEps : Double -> Double
machineEps x = unsafePerformIO $ foreign FFI_C "machine_eps" (Double -> IO Double) x
