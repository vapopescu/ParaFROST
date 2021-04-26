/***********************************************************************[pfsimp.cpp]
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

#pragma once
#include <thread>
#include <mutex>
#include <condition_variable>
#include <functional>

namespace pFROST {
	typedef std::function<void()> Job;

	class WorkerPool {
	protected:
		std::vector<std::thread>	_workers;
		std::vector<Job>			_jobQueue;
		std::mutex					_mutex;
		std::condition_variable		_workerCV;
		std::condition_variable		_poolCV;
		bool						_terminate;
		unsigned int				_waiting;

	public:
		WorkerPool();
		WorkerPool(unsigned int threads);
		~WorkerPool();

		void init(unsigned int threads);
		void destroy();
		void doWork(Job job);
		unsigned int count();
		void join();
	};
}
