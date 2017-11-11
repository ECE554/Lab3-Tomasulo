
#include <limits.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include "host.h"
#include "misc.h"
#include "machine.h"
#include "regs.h"
#include "memory.h"
#include "loader.h"
#include "syscall.h"
#include "dlite.h"
#include "options.h"
#include "stats.h"
#include "sim.h"
#include "decode.def"

#include "instr.h"

/* PARAMETERS OF THE TOMASULO'S ALGORITHM */

#define INSTR_QUEUE_SIZE         10

#define RESERV_INT_SIZE    4
#define RESERV_FP_SIZE     2
#define FU_INT_SIZE        2
#define FU_FP_SIZE         1

#define FU_INT_LATENCY     4
#define FU_FP_LATENCY      9

/* IDENTIFYING INSTRUCTIONS */

//unconditional branch, jump or call
#define IS_UNCOND_CTRL(op) (MD_OP_FLAGS(op) & F_CALL || \
                         MD_OP_FLAGS(op) & F_UNCOND)

//conditional branch instruction
#define IS_COND_CTRL(op) (MD_OP_FLAGS(op) & F_COND)

//floating-point computation
#define IS_FCOMP(op) (MD_OP_FLAGS(op) & F_FCOMP)

//integer computation
#define IS_ICOMP(op) (MD_OP_FLAGS(op) & F_ICOMP)

//load instruction
#define IS_LOAD(op)  (MD_OP_FLAGS(op) & F_LOAD)

//store instruction
#define IS_STORE(op) (MD_OP_FLAGS(op) & F_STORE)

//trap instruction
#define IS_TRAP(op) (MD_OP_FLAGS(op) & F_TRAP) 

#define USES_INT_FU(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_STORE(op))
#define USES_FP_FU(op) (IS_FCOMP(op))

#define WRITES_CDB(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_FCOMP(op))

#define IS_BRANCH(op) (IS_COND_CTRL(op) || IS_UNCOND_CTRL(op))

#define NUM_INPUT_REGS 3
#define NUM_OUTPUT_REGS 2

/* FOR DEBUGGING */

//prints info about an instruction
#define PRINT_INST(out,instr,str,cycle)	\
  myfprintf(out, "%d: %s", cycle, str);		\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

#define PRINT_REG(out,reg,str,instr) \
  myfprintf(out, "reg#%d %s ", reg, str);	\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

/* VARIABLES */

//instruction queue for tomasulo
static instruction_t* instr_queue[INSTR_QUEUE_SIZE];
//number of instructions in the instruction queue
static int instr_queue_size = 0;

//reservation stations (each reservation station entry contains a pointer to an instruction)
static instruction_t* reservINT[RESERV_INT_SIZE];
static instruction_t* reservFP[RESERV_FP_SIZE];

//functional units
static instruction_t* fuINT[FU_INT_SIZE];
static instruction_t* fuFP[FU_FP_SIZE];

//common data bus
static instruction_t* commonDataBus = NULL;

//The map table keeps track of which instruction produces the value for each register
static instruction_t* map_table[MD_TOTAL_REGS];

//the index of the last instruction fetched
static int fetch_index = 0;

/* FUNCTIONAL UNITS */


/* RESERVATION STATIONS */

int push_to_IFQ(instruction_t *instr) {
    int i = 0;
    for(; i < INSTR_QUEUE_SIZE; i++) {
        if(instr_queue[i] == NULL) {
            instr_queue[i] = instr;
            return 1;
        }
    }
    
    return 0;
}


instruction_t *pop_from_IFQ() {
    instruction_t *instr = instr_queue[0];
    int i = 1;
    
    for(; i < INSTR_QUEUE_SIZE; i++) {
        instr_queue[i-1] = instr_queue[i];
        instr_queue[i] = NULL;
    }
    
    return instr;
}

int push_to_resource(instruction_t** queue, int size, instruction_t* instr) {
    int i = 0;
    for(; i < size; i++) {
        if(queue[i] == NULL) {
            queue[i] = instr;
            return i;
        }
    }
    
    return -1;
}

void update_map_table(instruction_t *instr) {
    int i = 0;
    for(; i < NUM_OUTPUT_REGS; i++) {
        int r_out = instr->r_out[i];
        if(r_out != -1 && r_out != 0) {
            //checking for valid output reg
            map_table[r_out] = instr;
        }
    }
}

void clear_map_table(instruction_t *instr) {
    int i = 0;
    for(; i < NUM_OUTPUT_REGS; i++) {
        int r_out = instr->r_out[i];
        if(r_out != -1 && r_out != 0 && map_table[r_out] == instr) {
            //if this intruction was the last to rename r_out
            map_table[r_out] = NULL;
        }
    }
}

int instr_is_ready(instruction_t *instr) {
    int i = 0;
    int is_ready = 1;
    for(; i < NUM_INPUT_REGS; i++) {
        if(instr->Q[i] != NULL) is_ready = 0;
        //i think we'll set instr->Q[i] to NULL once CBD broadcasts?
        
    }
    
    return is_ready;
}


instruction_t *get_oldest_ready_int_instr() {
    int i;
    int j;
    instruction_t *oldest_instr = NULL;
    
    for(i = 0; i < RESERV_INT_SIZE; i++) {
        instruction_t *instr = reservINT[i];
        int in_FU = false;
        for(j = 0; j < FU_INT_SIZE; j++){
            if(fuINT[j] = instr) in_FU = true;
        }
        if(instr != NULL && !in_FU && instr_is_ready(instr)) {
            if(oldest_instr == NULL) oldest_instr = instr; //if the first instr in the reservation station is NULL
            else if(instr->index < oldest_instr->index) oldest_instr = instr;
        }
    }

    return oldest_instr;
}

//only called when there is space available in FP_FU
instruction_t *get_oldest_ready_fp_instr() {
    int i;
    int j;
    instruction_t *oldest_instr = NULL;
    
    for(i = 0; i < RESERV_FP_SIZE; i++) {
        instruction_t *instr = reservFP[i];
        
        int in_FU = false;
        for(j = 0; j < FU_FP_SIZE; j++){
            if(fuFP[j] = instr) in_FU = true;
        }
        
        if(instr != NULL && instr_is_ready(instr)) {
            if(oldest_instr == NULL) oldest_instr = instr; //if the first instr in the reservation station is NULL
            else if(instr->index < oldest_instr->index) oldest_instr = instr;
        }
    }

    return oldest_instr;
}

/* 
 * Description: 
 * 	Checks if simulation is done by finishing the very last instruction
 *      Remember that simulation is done only if the entire pipeline is empty
 * Inputs:
 * 	sim_insn: the total number of instructions simulated
 * Returns:
 * 	True: if simulation is finished
 */
static bool is_simulation_done(counter_t sim_insn) {

  /* ECE552: YOUR CODE GOES HERE */
//    int rtn = 0;
//    if (commonDataBus != NULL && commonDataBus->index >= sim_insn - 1) rtn = true;
//    rtn = false;
//    commonDataBus = NULL;
//    return rtn;
    if(commonDataBus != NULL) return false;
    
    int i;
    for(i = 0; i < RESERV_INT_SIZE; i++) {
        if(reservINT[i] != NULL) return false;
    }

    for(i = 0; i < RESERV_FP_SIZE; i++) {
        if(reservFP[i] != NULL) return false;
    }
    
    for(i = 0; i < INSTR_QUEUE_SIZE; i++) {
        if(instr_queue[i] != NULL) return false;
    }
    
    return true;
    
    //ECE552: you can change this as needed; we've added this so the code provided to you compiles
}

/* 
 * Description: 
 * 	Retires the instruction from writing to the Common Data Bus
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void CDB_To_retire(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
    if (commonDataBus == NULL) return;

    int i;
    int j;
    //For all instrs in res station, reset their Q if it is in CDB
    for(i = 0; i < RESERV_INT_SIZE; i++) {
        instruction_t *instr = reservINT[i];
        if (instr == NULL) continue;
        for (j = 0; j < NUM_INPUT_REGS; j++) {
            if (instr->Q[j] == commonDataBus) {
                instr->Q[j] = NULL;
                commonDataBus = NULL;
            }
        }
    }

    //For all instrs in res station, reset their Q if it is in CDB
    for(i = 0; i < RESERV_FP_SIZE; i++) {
        instruction_t *instr = reservFP[i];
        if (instr == NULL) continue;
        for (j = 0; j < NUM_INPUT_REGS; j++) {
            if (instr->Q[j] == commonDataBus) {
                instr->Q[j] = NULL;
                commonDataBus = NULL;
            }
        }
    }
}


/* 
 * Description: 
 * 	Moves an instruction from the execution stage to common data bus (if possible)
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void execute_To_CDB(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
    int i;
    int cdbINT = 0;
    int cdb_index = -1;
    for(i = 0; i < FU_INT_SIZE; i++) {
        if(fuINT[i] != NULL) {
            instruction_t *instr = fuINT[i];
            if (current_cycle - instr->tom_execute_cycle >= FU_FP_LATENCY) { // Ready to broadcast
                if (commonDataBus == NULL){
                     commonDataBus = instr;
                     cdbINT = true;
                     cdb_index = i;
                }
                else if (instr->index < commonDataBus->index){
                    commonDataBus = instr;
                    cdbINT = true;
                    cdb_index = i;
                }
            }
        }
    }

    for(i = 0; i < FU_FP_SIZE; i++) {
        if(fuFP[i] != NULL) {
            instruction_t *instr = fuFP[i];
            if (current_cycle - instr->tom_execute_cycle >= FU_FP_LATENCY) { // Ready to broadcast
                if (commonDataBus == NULL){
                     commonDataBus = instr;
                     cdbINT = false;
                     cdb_index = i;
                }
                else if (instr->index < commonDataBus->index){
                     commonDataBus = instr;
                     cdbINT = false;
                     cdb_index = i;
                }
            }
        }
    }

    if (commonDataBus != NULL) {
        commonDataBus->tom_cdb_cycle = current_cycle; //Only the last set instr (oldest) gets to use the CDB
        if (cdbINT) {
            fuINT[cdb_index] = NULL;
            for(i = 0; i < RESERV_INT_SIZE; i++) {
                if(reservINT[i] == commonDataBus) {
                    reservINT[i] = NULL;
                    break;
                }
            }
        }
            else {
                fuFP[cdb_index] = NULL;
                for(i = 0; i < RESERV_FP_SIZE; i++) {
                    if(reservFP[i] == commonDataBus) {
                        reservFP[i] = NULL;
                        break;
                    }
                }
            }
    }
}

/* 
 * Description: 
 * 	Moves instruction(s) from the issue to the execute stage (if possible). We prioritize old instructions
 *      (in program order) over new ones, if they both contend for the same functional unit.
 *      All RAW dependences need to have been resolved with stalls before an instruction enters execute.
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void issue_To_execute(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
    //check if we can send an INT instruction through
    int i;
    for(i = 0; i < FU_INT_SIZE; i++) {
        if(fuINT[i] == NULL) {
            //can add an instruction
            instruction_t *instr = get_oldest_ready_int_instr();
            if(instr != NULL && instr->tom_issue_cycle  < current_cycle) {
                fuINT[i] = instr;
                instr->tom_execute_cycle = current_cycle;
            }
        }
    }
    
    //check if we can send an FP instruction through
    for(i = 0; i < FU_FP_SIZE; i++) {
        if(fuFP[i] == NULL) {
            //can add an instruction
            instruction_t *instr = get_oldest_ready_fp_instr();
            if(instr != NULL && instr->tom_issue_cycle  < current_cycle) {
                fuFP[i] = instr;
                instr->tom_execute_cycle = current_cycle;
            }
        }
    }
}

/* 
 * Description: 
 * 	Moves instruction(s) from the dispatch stage to the issue stage
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void dispatch_To_issue(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
    
    int i;
    
    //since only one instruction enters dispatch in one cycle there should  only be one instruction with an unassigned issue cyle
    
    for(i = 0; i < RESERV_INT_SIZE; i++) {
        instruction_t *instr = reservINT[i];
        if(instr && instr->tom_issue_cycle == 0 && instr->tom_dispatch_cycle < current_cycle) {
            instr->tom_issue_cycle = current_cycle;
        }
    }
    
    //check if we can send an FP instruction through
    for(i = 0; i < RESERV_FP_SIZE; i++) {
        instruction_t *instr = reservFP[i];
        if(instr && instr->tom_issue_cycle == 0 && instr->tom_dispatch_cycle < current_cycle) {
            instr->tom_issue_cycle = current_cycle;
        }
    }
}

/* 
 * Description: 
 * 	Grabs an instruction from the instruction trace (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	None
 */
void fetch(instruction_trace_t* trace) {

  /* ECE552: YOUR CODE GOES HERE */
    instruction_t* instr = get_instr(trace, fetch_index);
    
    while(IS_TRAP(instr->op) || instr->op == 0) instr = get_instr(trace, ++fetch_index);
    
    int pushed = push_to_IFQ(instr);
    if(pushed) {
        fetch_index++;
    }
}

/* 
 * Description: 
 * 	Calls fetch and dispatches an instruction at the same cycle (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void fetch_To_dispatch(instruction_trace_t* trace, int current_cycle) {

  fetch(trace);
  
  /* ECE552: YOUR CODE GOES HERE */
    instruction_t *next_instr = instr_queue[0];
    
    if(IS_BRANCH(next_instr->op)) {
        pop_from_IFQ();
        next_instr->tom_dispatch_cycle = current_cycle;
        return;
    }
    
    if(USES_INT_FU(next_instr->op)) {
        int i;
        int rs_idx = -1;
        for(i = 0; i < RESERV_INT_SIZE; i++) {
            if(reservINT[i] == NULL) {
                reservINT[i] = next_instr;
                rs_idx = i;
                break;
            }
        }

        if(rs_idx != -1) { //There was room for it in RS
            pop_from_IFQ(); //Remove from from of IFQ
            
            //update mapTable and dependencies in RS
            for(i = 0; i < NUM_INPUT_REGS; i++) {
                if (next_instr->r_in[i] != -1) next_instr->Q[i] = map_table[next_instr->r_in[i]]; //Set RAW HAZARDS
                else next_instr->Q[i] = NULL;
            }
            update_map_table(next_instr);
            
            next_instr->tom_dispatch_cycle = current_cycle;
            return;
        }
    }
    
    if(USES_FP_FU(next_instr->op)) {
        int i;
        int rs_idx = -1;
        for(i = 0; i < RESERV_FP_SIZE; i++) {
            if(reservFP[i] == NULL) {
                reservFP[i] = next_instr;
                rs_idx = i;
                break;
            }
        }

        if(rs_idx != -1) {
            pop_from_IFQ();
            
            //update mapTable and dependencies in RS
            for(i = 0; i < NUM_INPUT_REGS; i++) {
                if (next_instr->r_in[i] != -1) next_instr->Q[i] = map_table[next_instr->r_in[i]]; //Set RAW HAZARDS
                else next_instr->Q[i] = NULL;
            }
            update_map_table(next_instr);
            
            next_instr->tom_dispatch_cycle = current_cycle;
            return;
        }
    }
}

void debug_cycle(int cycle);

/* 
 * Description: 
 * 	Performs a cycle-by-cycle simulation of the 4-stage pipeline
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	The total number of cycles it takes to execute the instructions.
 * Extra Notes:
 * 	sim_num_insn: the number of instructions in the trace
 */
counter_t runTomasulo(instruction_trace_t* trace)
{
  //initialize instruction queue
  int i;
  for (i = 0; i < INSTR_QUEUE_SIZE; i++) {
    instr_queue[i] = NULL;
  }

  //initialize reservation stations
  for (i = 0; i < RESERV_INT_SIZE; i++) {
      reservINT[i] = NULL;
  }

  for(i = 0; i < RESERV_FP_SIZE; i++) {
      reservFP[i] = NULL;
  }

  //initialize functional units
  for (i = 0; i < FU_INT_SIZE; i++) {
    fuINT[i] = NULL;
  }

  for (i = 0; i < FU_FP_SIZE; i++) {
    fuFP[i] = NULL;
  }

  //initialize map_table to no producers
  int reg;
  for (reg = 0; reg < MD_TOTAL_REGS; reg++) {
    map_table[reg] = NULL;
  }
  
  int cycle = 1;
  while (true) {
    if (cycle % 100 == 0) printf("Cycle #: %d \n", cycle);
     /* ECE552: YOUR CODE GOES HERE */
    //   fetch(trace, cycle);
                int debug = 0;    
                if(debug) printf("F2D\n");
      fetch_To_dispatch(trace, cycle);
                if(debug) printf("D2I\n");
      dispatch_To_issue(cycle);
                if(debug) printf("I2E\n");
      issue_To_execute(cycle);
                if(debug) printf("E2C\n");
      execute_To_CDB(cycle);
                if(debug) printf("C2R\n");
      CDB_To_retire(cycle);


//                debug_cycle(cycle);

     cycle++;
     if (is_simulation_done(sim_num_insn))
        break;
  }
  
  return cycle; 
}

void debug_cycle(int cycle) {
    printf("Cycle: %d\n", cycle);

    int i = 0;
    int count = 0;

    for(i = 0; i < INSTR_QUEUE_SIZE; i++) {
        if(instr_queue[i] != NULL) {
            count++;
             printf("\tinstr: %d->", instr_queue[i]->index);
        }
    }
    printf("\tNum In IFQ: %d\n\n", count);
    count = 0;
    for (i = 0; i < RESERV_INT_SIZE; i++) {
        if (reservINT[i] != NULL) {
            count++;
            printf("\tinstr: %d,", reservINT[i]->index);
        }
    }
    printf("\tNum In rINT: %d\n", count);
    count = 0;
    for (i = 0; i < RESERV_FP_SIZE; i++) {
        if (reservFP[i] != NULL) {
            count++;
            printf("\tinstr: %d,", reservFP[i]->index);
        }
    }
    printf("\tNum In rFP: %d\n\n", count);
    count = 0;
    for (i = 0; i < FU_INT_SIZE; i++) {
        if (fuINT[i] != NULL) count++;
    }
    printf("\tNum In fuINT: %d\n", count);
    count = 0;
    for (i = 0; i < FU_FP_SIZE; i++) {
        if (fuFP[i] != NULL) count++;
    }
    printf("\tNum In fuFP: %d\n\n", count);
    printf("\tID In CDB: %d\n\n", commonDataBus == NULL ? -1 : commonDataBus->index);
    
}
