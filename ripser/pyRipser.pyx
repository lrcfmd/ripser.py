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


@cython.boundscheck(False)
@cython.wraparound(False)
def doRipsFiltrationDMSparseCycles(np.ndarray[int,ndim=1,mode="c"] I not None, np.ndarray[int,ndim=1,mode="c"] J not None, np.ndarray[float,ndim=1,mode="c"] V not None, int N, int maxHomDim, float thresh=-1, int coeff=2, bint do_cocycles=0):
	cdef int NEdges = I.size
	res = pyRips.rips_dm_sparse_cycles(&I[0], &J[0], &V[0], NEdges, N, coeff, maxHomDim, thresh)
	return res
