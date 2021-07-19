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
#include <atomic>

namespace pFROST {
	typedef std::function<void()> Job;

	class WorkerPool {
	protected:
		std::vector<std::thread>			_workers;
		std::vector<Job>					_jobQueue;
		mutable std::mutex					_mutex;
		mutable std::condition_variable		_workerCV;
		mutable std::condition_variable		_poolCV;
		bool								_terminate;
		unsigned int						_waiting;
		unsigned int						_max_batch;

	public:
		inline void init(unsigned int threads, unsigned int max_batch)
		{
			_workers.clear();
			_jobQueue.clear();
			_terminate = false;
			_waiting = 0;
			_max_batch = max_batch;
			if (threads == 0) threads = 1;

			for (unsigned int i = 0; i < threads; i++) {
				_workers.push_back(std::thread([this] {
					while (true) {
						std::unique_lock<std::mutex> lock(_mutex);
						std::function<bool()> condition = [this] { return !_jobQueue.empty() || _terminate; };
						if (!condition()) {
							_waiting++;
							_poolCV.notify_one();
							_workerCV.wait(lock, condition);
							_waiting--;
						}

						if (_terminate) break;
						Job job = std::move(_jobQueue.back());
						_jobQueue.pop_back();
						lock.unlock();

						job();
					}
				}));
			}
		}

		inline void destroy() {
			if (_terminate) return;
			_terminate = true;
			_workerCV.notify_all();

			for (auto& w : _workers) {
				w.join();
			}

			_workers.clear();
			_jobQueue.clear();
		}

		inline unsigned int count() { return (unsigned int)_workers.size(); }

		inline void doWork(const Job& job)
		{
			std::unique_lock<std::mutex> lock(_mutex);

			for (unsigned int i = 0; i < _workers.size(); i++) {
				_jobQueue.push_back(job);
			}

			_workerCV.notify_all();
		}

		template<class IntType, class Function>
		inline void doWorkForEach(const IntType& begin, const IntType& end, const IntType& maxBatch, const Function& job)
		{
			std::unique_lock<std::mutex> lock(_mutex);
			IntType idx = begin;
			IntType batchSize = (end - begin) / (IntType)_workers.size();
			IntType remainder = (end - begin) % (IntType)_workers.size();
			if (maxBatch > 0 && batchSize > maxBatch) {
				batchSize = maxBatch;
				remainder = 0;
			}

			while (idx < end) {
				IntType thisBatchSize = idx < remainder ? batchSize + 1 : batchSize;
				if (idx + thisBatchSize > end) thisBatchSize = end - idx;
				_jobQueue.push_back([this, idx, thisBatchSize, job] {
					for (IntType j = idx; j < idx + thisBatchSize; j++)
						job(j);
				});
				idx += thisBatchSize;
			}

			_workerCV.notify_all();
		}

		template<class IntType, class Function>
		inline void doWorkForEach(const IntType& begin, const IntType& end, const Function& job)
		{
			doWorkForEach(begin, end, (IntType)_max_batch, job);
		}

		inline void join() const {
			std::unique_lock<std::mutex> lock(_mutex);
			_poolCV.wait(lock, [this] { return _jobQueue.empty() && _waiting == _workers.size(); });
		}

		inline int getID() const {
			std::thread::id realId = std::this_thread::get_id();

			for (int i = 0; i < _workers.size(); i++) {
				if (realId == _workers[i].get_id()) return i;
			}

			return -1;
		}
	};
}
