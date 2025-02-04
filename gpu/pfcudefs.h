/***********************************************************************[pfcudefs.h]
Copyright(c) 2020, Muhammad Osama - Anton Wijs,
Technische Universiteit Eindhoven (TU/e).

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
**********************************************************************************/

#ifndef __CU_DEFS_
#define __CU_DEFS_  

#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <cuda.h>
#include <device_launch_parameters.h>
#include "pflogging.h"

namespace pFROST {

	namespace SIGmA {

		#if !defined(_PFROST_H_)
		#define _PFROST_H_ inline __host__
		#endif
		#if !defined(_PFROST_D_)
		#define _PFROST_D_ __forceinline__ __device__
		#endif
		#if !defined(_PFROST_H_D_)
		#define _PFROST_H_D_ inline __host__ __device__
		#endif
		#if defined(DEBUG) || defined(_DEBUG) 
		#define LOGERR(MESSAGE)	\
				do { \
					cudaError_t ERR = cudaGetLastError(); \
					if (cudaSuccess != ERR) { \
						PFLOGEN("%s(%i): %s due to (%d) %s", __FILE__, __LINE__, MESSAGE, static_cast<int>(ERR), cudaGetErrorString(ERR)); \
						cudaDeviceReset(); \
						exit(1); \
					} \
				} \
				while(0)
		#else
		#define LOGERR(MESSAGE)	do { } while(0)
		#endif

		__forceinline__ void	CHECK(cudaError_t returncode)
		{
		#if defined(DEBUG) || defined(_DEBUG)
			if (returncode != cudaSuccess) {
				PFLOGEN("CUDA runtime failure due to %s", cudaGetErrorString(returncode));
				cudaDeviceReset();
				exit(1);
			}
		#endif
		}

		__forceinline__ void	sync(const cudaStream_t& stream = 0) {
			CHECK(cudaStreamSynchronize(stream));
		}

		__forceinline__ void	syncAll() {
			CHECK(cudaDeviceSynchronize());
		}

	}
}

#endif
