# distutils: language = c++

cimport numpy as np
cimport ripser.pyRips as pyRips
import cython

@cython.boundscheck(False)
@cython.wraparound(False)
def doRipsFiltrationDMCycles(np.ndarray[float,ndim=1,mode="c"] DParam not None, int maxHomDim, float thresh=-1, int coeff=2):

	cdef int N = DParam.shape[0]

	res = pyRips.rips_dm_cycles(&DParam[0], N, coeff, maxHomDim, thresh)

	return res
