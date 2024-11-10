/* This file is derived from source code for the Nachos
   instructional operating system.  The Nachos copyright notice
   is reproduced in full below. */

/* Copyright (c) 1992-1996 The Regents of the University of California.
   All rights reserved.

   Permission to use, copy, modify, and distribute this software
   and its documentation for any purpose, without fee, and
   without written agreement is hereby granted, provided that the
   above copyright notice and the following two paragraphs appear
   in all copies of this software.

   IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO
   ANY PARTY FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR
   CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OF THIS SOFTWARE
   AND ITS DOCUMENTATION, EVEN IF THE UNIVERSITY OF CALIFORNIA
   HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

   THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY
   WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
   WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
   PURPOSE.  THE SOFTWARE PROVIDED HEREUNDER IS ON AN "AS IS"
   BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION TO
   PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
   MODIFICATIONS.
   */

#include "threads/synch.h"
#include "threads/interrupt.h"
#include "threads/thread.h"
#include <stdio.h>
#include <string.h>

bool sema_compare_priority(const struct list_elem *l, const struct list_elem *s, void *aux UNUSED);

/* Initializes semaphore SEMA to VALUE.  A semaphore is a
   nonnegative integer along with two atomic operators for
   manipulating it:

   - down or "P": wait for the value to become positive, then
   decrement it.

   - up or "V": increment the value (and wake up one waiting
   thread, if any). */
void sema_init(struct semaphore *sema, unsigned value) {
    ASSERT(sema != NULL);

    sema->value = value;
    list_init(&sema->waiters);
}

/* 세마포어에 대한 다운(Down) 또는 "P" 연산입니다. 세마포어의 값이 양수가 될 때까지
   대기한 후 원자적으로 값을 감소시킵니다.

   이 함수는 슬립 상태가 될 수 있으므로 인터럽트 핸들러 내에서 호출되어서는 안 됩니다.
   인터럽트가 비활성화된 상태에서 호출될 수 있지만, 만약 슬립 상태가 되면
   다음에 스케줄링되는 스레드가 인터럽트를 다시 활성화할 것입니다.
   이것이 sema_down 함수입니다. */
void sema_down(struct semaphore *sema) {
    enum intr_level old_level; // 인터럽트 레벨 변수 선언

    ASSERT(sema != NULL);    // 세마포어가 NULL이 아닌지 검사
    ASSERT(!intr_context()); // 인터럽트 컨텍스트인지 검사

    old_level = intr_disable(); // 인터럽트 비활성화
    while (sema->value == 0) {
        list_insert_ordered(&sema->waiters, &thread_current()->elem, compare_priority,
                            0); // 현재 스레드를 세마포어의 대기 목록에 내림차순으로 삽입
        thread_block();         // 현재 스레드를 블록 상태로 전환
    }
    sema->value--;             // 세마포어 값 감소
    intr_set_level(old_level); // 인터럽트 레벨 복원
}

/* 세마포어에 대한 다운(Down) 또는 "P" 연산을 수행하지만, 세마포어 값이 이미 0이 아닌
   경우에만 수행합니다. 세마포어 값이 감소되면 true를 반환하고, 그렇지 않으면 false를
   반환합니다.

   이 함수는 인터럽트 핸들러에서 호출될 수 있습니다. */
bool sema_try_down(struct semaphore *sema) {
    enum intr_level old_level;
    bool success;

    ASSERT(sema != NULL);

    old_level = intr_disable();
    if (sema->value > 0) {
        sema->value--;
        success = true;
    } else
        success = false;
    intr_set_level(old_level);

    return success;
}

/* 세마포어에 대한 업(Up) 또는 "V" 연산입니다. 세마포어의 값을 증가시키고,
   세마포어를 기다리는 스레드가 있다면 그 중 하나를 깨웁니다.

   이 함수는 인터럽트 핸들러 내에서 호출될 수 있습니다. */
void sema_up(struct semaphore *sema) {
    enum intr_level old_level; // 인터럽트 레벨 변수 선언

    ASSERT(sema != NULL); // 세마포어가 NULL이 아닌지 검사

    old_level = intr_disable();                         // 인터럽트 비활성화
    if (!list_empty(&sema->waiters)) {                  // 세마포어의 대기 목록이 비어있지 않으면
        list_sort(&sema->waiters, compare_priority, 0); // 대기 목록을 우선순위에 따라 정렬
        thread_unblock(list_entry(list_pop_front(&sema->waiters), struct thread, elem)); // 가장 앞에 있는 스레드를 깨움
    }
    sema->value++;             // 세마포어 값 증가
    thread_preemption();      // 선점 활성화
    intr_set_level(old_level); // 인터럽트 레벨 복원
}

static void sema_test_helper(void *sema_);

/* Self-test for semaphores that makes control "ping-pong"
   between a pair of threads.  Insert calls to printf() to see
   what's going on. */
void sema_self_test(void) {
    struct semaphore sema[2];
    int i;

    printf("Testing semaphores...");
    sema_init(&sema[0], 0);
    sema_init(&sema[1], 0);
    thread_create("sema-test", PRI_DEFAULT, sema_test_helper, &sema);
    for (i = 0; i < 10; i++) {
        sema_up(&sema[0]);
        sema_down(&sema[1]);
    }
    printf("done.\n");
}

/* Thread function used by sema_self_test(). */
static void sema_test_helper(void *sema_) {
    struct semaphore *sema = sema_;
    int i;

    for (i = 0; i < 10; i++) {
        sema_down(&sema[0]);
        sema_up(&sema[1]);
    }
}

/* Initializes LOCK.  A lock can be held by at most a single
   thread at any given time.  Our locks are not "recursive", that
   is, it is an error for the thread currently holding a lock to
   try to acquire that lock.

   A lock is a specialization of a semaphore with an initial
   value of 1.  The difference between a lock and such a
   semaphore is twofold.  First, a semaphore can have a value
   greater than 1, but a lock can only be owned by a single
   thread at a time.  Second, a semaphore does not have an owner,
   meaning that one thread can "down" the semaphore and then
   another one "up" it, but with a lock the same thread must both
   acquire and release it.  When these restrictions prove
   onerous, it's a good sign that a semaphore should be used,
   instead of a lock. */
void lock_init(struct lock *lock) {
    ASSERT(lock != NULL);

    lock->holder = NULL;
    sema_init(&lock->semaphore, 1);
}

/* Acquires LOCK, sleeping until it becomes available if
   necessary.  The lock must not already be held by the current
   thread.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but interrupts will be turned back on if
   we need to sleep. */
void lock_acquire(struct lock *lock) {
    ASSERT(lock != NULL);
    ASSERT(!intr_context());
    ASSERT(!lock_held_by_current_thread(lock));

    sema_down(&lock->semaphore);
    lock->holder = thread_current();
}

/* Tries to acquires LOCK and returns true if successful or false
   on failure.  The lock must not already be held by the current
   thread.

   This function will not sleep, so it may be called within an
   interrupt handler. */
bool lock_try_acquire(struct lock *lock) {
    bool success;

    ASSERT(lock != NULL);
    ASSERT(!lock_held_by_current_thread(lock));

    success = sema_try_down(&lock->semaphore);
    if (success)
        lock->holder = thread_current();
    return success;
}

/* Releases LOCK, which must be owned by the current thread.
   This is lock_release function.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to release a lock within an interrupt
   handler. */
void lock_release(struct lock *lock) {
    ASSERT(lock != NULL);
    ASSERT(lock_held_by_current_thread(lock));

    lock->holder = NULL;
    sema_up(&lock->semaphore);
}

/* Returns true if the current thread holds LOCK, false
   otherwise.  (Note that testing whether some other thread holds
   a lock would be racy.) */
bool lock_held_by_current_thread(const struct lock *lock) {
    ASSERT(lock != NULL);

    return lock->holder == thread_current();
}

/* One semaphore in a list. */
struct semaphore_elem {
    struct list_elem elem;      /* List element. */
    struct semaphore semaphore; /* This semaphore. */
};

/* Initializes condition variable COND.  A condition variable
   allows one piece of code to signal a condition and cooperating
   code to receive the signal and act upon it. */
void cond_init(struct condition *cond) {
    ASSERT(cond != NULL);

    list_init(&cond->waiters);
}

/* 원자적으로 LOCK을 해제하고 다른 코드에 의해 COND가 시그널될 때까지 대기합니다.
   COND가 시그널되면 반환하기 전에 LOCK을 다시 획득합니다.
   이 함수를 호출하기 전에는 반드시 LOCK을 보유하고 있어야 합니다.

   이 함수로 구현된 모니터는 "Hoare" 스타일이 아닌 "Mesa" 스타일입니다.
   즉, 시그널을 보내고 받는 것이 원자적 연산이 아닙니다.
   따라서 일반적으로 호출자는 대기가 완료된 후 조건을 다시 확인해야 하며,
   필요한 경우 다시 대기해야 합니다.

   하나의 조건 변수는 단 하나의 락과만 연관되지만,
   하나의 락은 여러 개의 조건 변수와 연관될 수 있습니다.
   즉, 락에서 조건 변수로의 일대다 매핑이 존재합니다.

   이 함수는 슬립 상태가 될 수 있으므로 인터럽트 핸들러 내에서 호출되어서는 안 됩니다.
   인터럽트가 비활성화된 상태에서 이 함수를 호출할 수 있지만,
   슬립이 필요한 경우 인터럽트가 다시 활성화됩니다. */
void cond_wait(struct condition *cond, struct lock *lock) {
    struct semaphore_elem waiter;

    ASSERT(cond != NULL);                      // cond가 NULL이 아닌지 검사
    ASSERT(lock != NULL);                      // lock이 NULL이 아닌지 검사
    ASSERT(!intr_context());                   // 인터럽트 컨텍스트인지 검사
    ASSERT(lock_held_by_current_thread(lock)); // lock을 현재 스레드가 보유하고 있는지 검사

    sema_init(&waiter.semaphore, 0); // waiter의 세마포어 초기화
    list_insert_ordered(&cond->waiters, &waiter.elem, sema_compare_priority,
                        0);       // waiter를 대기 목록에 내림차순으로 삽입
    lock_release(lock);           // lock 해제
    sema_down(&waiter.semaphore); // waiter의 세마포어 다운
    lock_acquire(lock);           // lock 획득
}

/* COND에서 대기 중인 스레드가 있다면(LOCK으로 보호됨),
   이 함수는 그 중 하나에게 대기 상태에서 깨어나라는 시그널을 보냅니다.
   이 함수를 호출하기 전에는 반드시 LOCK을 보유하고 있어야 합니다.

   인터럽트 핸들러는 락을 획득할 수 없으므로,
   인터럽트 핸들러 내에서 조건 변수에 시그널을 보내는 것은 의미가 없습니다. */
void cond_signal(struct condition *cond, struct lock *lock UNUSED) {
    ASSERT(cond != NULL);                      // cond가 NULL이 아닌지 검사
    ASSERT(lock != NULL);                      // lock이 NULL이 아닌지 검사
    ASSERT(!intr_context());                   // 인터럽트 컨텍스트인지 검사
    ASSERT(lock_held_by_current_thread(lock)); // lock을 현재 스레드가 보유하고 있는지 검사

    if (!list_empty(&cond->waiters)) {                       // 대기 목록이 비어있지 않으면
        list_sort(&cond->waiters, sema_compare_priority, 0); // 대기 목록을 우선순위에 따라 정렬
        sema_up(&list_entry(list_pop_front(&cond->waiters), struct semaphore_elem, elem)
                     ->semaphore); // 가장 앞에 있는 스레드의 세마포어 업
    }
}

/* COND에서 대기 중인 모든 스레드를 깨웁니다(LOCK으로 보호됨).
   이 함수를 호출하기 전에는 반드시 LOCK을 보유하고 있어야 합니다.

   인터럽트 핸들러는 락을 획득할 수 없으므로,
   인터럽트 핸들러 내에서 조건 변수에 시그널을 보내는 것은 의미가 없습니다. */
void cond_broadcast(struct condition *cond, struct lock *lock) {
    ASSERT(cond != NULL);                      // cond가 NULL이 아닌지 검사
    ASSERT(lock != NULL);                      // lock이 NULL이 아닌지 검사
    ASSERT(!intr_context());                   // 인터럽트 컨텍스트인지 검사
    ASSERT(lock_held_by_current_thread(lock)); // lock을 현재 스레드가 보유하고 있는지 검사

    while (!list_empty(&cond->waiters)) // 대기 목록이 비어있지 않으면
        cond_signal(cond, lock);        // 대기 목록에 있는 모든 스레드에게 시그널 보냄
}

/* 세마포어의 대기 목록에서 스레드의 우선순위를 비교하는 함수 */
bool sema_compare_priority(const struct list_elem *l, const struct list_elem *s, void *aux UNUSED) {
    struct semaphore_elem *l_sema = list_entry(l, struct semaphore_elem, elem); // l 요소를 semaphore_elem 구조체로 변환
    struct semaphore_elem *s_sema = list_entry(s, struct semaphore_elem, elem); // s 요소를 semaphore_elem 구조체로 변환

    struct list *waiter_l_sema = &(l_sema->semaphore.waiters); // l_sema의 대기 목록
    struct list *waiter_s_sema = &(s_sema->semaphore.waiters); // s_sema의 대기 목록

    return list_entry(list_begin(waiter_l_sema), struct thread, elem)->priority >
           list_entry(list_begin(waiter_s_sema), struct thread, elem)
               ->priority; // l_sema의 대기 목록에서 첫 번째 스레드의 우선순위가 s_sema의 대기 목록에서 첫 번째 스레드의
                           // 우선순위보다 높으면 true, 아니면 false 반환
}