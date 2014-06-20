/*
 * Read-Copy Update mechanism for mutual exclusion (tree-based version)
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-2.0.html.
 *
 * Copyright IBM Corporation, 2008
 *
 * Author: Dipankar Sarma <dipankar@in.ibm.com>
 *	   Paul E. McKenney <paulmck@linux.vnet.ibm.com> Hierarchical algorithm
 *
 * Based on the original work by Paul McKenney <paulmck@us.ibm.com>
 * and inputs from Rusty Russell, Andrea Arcangeli and Andi Kleen.
 *
 * For detailed explanation of Read-Copy Update mechanism see -
 *	Documentation/RCU
 */

#ifndef __LINUX_RCUTREE_H
#define __LINUX_RCUTREE_H

void rcu_note_context_switch(int cpu);
#ifndef CONFIG_RCU_NOCB_CPU_ALL
int rcu_needs_cpu(int cpu, unsigned long *delta_jiffies);
#endif /* #ifndef CONFIG_RCU_NOCB_CPU_ALL */
void rcu_cpu_stall_reset(void);

/*
 * Note a virtualization-based context switch.  This is simply a
 * wrapper around rcu_note_context_switch(), which allows TINY_RCU
 * to save a few bytes.
 */
static inline void rcu_virt_note_context_switch(int cpu)
{
	rcu_note_context_switch(cpu);
}

DECLARE_PER_CPU(int, rcu_cond_resched_mask);
void rcu_resched(void);

/* Is it time to report RCU quiescent states? */
static inline bool rcu_should_resched(void)
{
	return raw_cpu_read(rcu_cond_resched_mask);
}

/* Report quiescent states to RCU if it is time to do so. */
static inline void __rcu_cond_resched(void)
{
	if (unlikely(rcu_should_resched()))
		rcu_resched();
}

/*
 * Report quiescent states to RCU in kernels that are not configured
 * for low-latency kernel-intensive workloads.
 */
static inline void rcu_cond_resched(void)
{
#ifdef CONFIG_RCU_COND_RESCHED_QS
	__rcu_cond_resched();
#endif /* #ifdef CONFIG_RCU_COND_RESCHED_QS */
}

/**
 * cond_resched_rcu_qs - Report potential quiescent states to RCU
 *
 * This macro resembles cond_resched(), except that it is defined to
 * report potential quiescent states to RCU even if the cond_resched()
 * machinery were to be shut off, as some advocate for PREEMPT kernels.
 */
#define cond_resched_rcu_qs() \
do { \
	__rcu_cond_resched(); \
	cond_resched(); \
} while (0)

void synchronize_rcu_bh(void);
void synchronize_sched_expedited(void);
void synchronize_rcu_expedited(void);

void kfree_call_rcu(struct rcu_head *head, void (*func)(struct rcu_head *rcu));

/**
 * synchronize_rcu_bh_expedited - Brute-force RCU-bh grace period
 *
 * Wait for an RCU-bh grace period to elapse, but use a "big hammer"
 * approach to force the grace period to end quickly.  This consumes
 * significant time on all CPUs and is unfriendly to real-time workloads,
 * so is thus not recommended for any sort of common-case code.  In fact,
 * if you are using synchronize_rcu_bh_expedited() in a loop, please
 * restructure your code to batch your updates, and then use a single
 * synchronize_rcu_bh() instead.
 *
 * Note that it is illegal to call this function while holding any lock
 * that is acquired by a CPU-hotplug notifier.  And yes, it is also illegal
 * to call this function from a CPU-hotplug notifier.  Failing to observe
 * these restriction will result in deadlock.
 */
static inline void synchronize_rcu_bh_expedited(void)
{
	synchronize_sched_expedited();
}

void rcu_barrier(void);
void rcu_barrier_bh(void);
void rcu_barrier_sched(void);
unsigned long get_state_synchronize_rcu(void);
void cond_synchronize_rcu(unsigned long oldstate);

extern unsigned long rcutorture_testseq;
extern unsigned long rcutorture_vernum;
long rcu_batches_completed(void);
long rcu_batches_completed_bh(void);
long rcu_batches_completed_sched(void);
void show_rcu_gp_kthreads(void);

void rcu_force_quiescent_state(void);
void rcu_bh_force_quiescent_state(void);
void rcu_sched_force_quiescent_state(void);

void exit_rcu(void);

void rcu_scheduler_starting(void);
extern int rcu_scheduler_active __read_mostly;

bool rcu_is_watching(void);

#endif /* __LINUX_RCUTREE_H */
