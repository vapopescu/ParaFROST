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

#include "pfworker.h"

using namespace pFROST;

WorkerPool::WorkerPool() {
	init(std::thread::hardware_concurrency());
}

WorkerPool::WorkerPool(unsigned int threads) {
	init(threads);
}

WorkerPool::~WorkerPool() {
	destroy();
}

void WorkerPool::init(unsigned int threads) {
	_terminate = false;
	_waiting = 0;
	if (threads == 0) threads = 1;

	for (int i = 0; i < threads; i++) {
		_workers.emplace_back(std::thread([this] {
			while (true) {
				Job job;

				{
					std::unique_lock<std::mutex> lock(_mutex);
					std::function<bool()> condition = [this] { return !_jobQueue.empty() || _terminate; };
					if (!condition()) {
						_waiting++;
						_poolCV.notify_one();
						_workerCV.wait(lock, condition);
						_waiting--;
					}

					if (_terminate) return;
					job = _jobQueue.back();
					_jobQueue.pop_back();
				}

				job();
			}
		}));
	}
}

void WorkerPool::destroy() {
	if (_terminate) return;
	_terminate = true;
	_workerCV.notify_all();

	for (auto& w : _workers) {
		w.join();
	}

	_workers.clear();
	_jobQueue.clear();
}

void WorkerPool::doWork(Job job) {
	std::unique_lock<std::mutex>(_mutex);

	for (int i = 0; i < _workers.size(); i++) {
		_jobQueue.push_back(job);
	}

	_workerCV.notify_all();
}

unsigned int WorkerPool::count() {
	return _workers.size();
}

void WorkerPool::join() {
	std::unique_lock<std::mutex> lock(_mutex);
	std::function<bool()> condition = [this] { return _waiting == _workers.size(); };
	if (!condition()) _poolCV.wait(lock, condition);
	return;
}
