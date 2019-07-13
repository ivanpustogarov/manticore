#!/usr/bin/env python

'''
Rough concolic execution implementation

Limitations
- tested only on the simpleassert example program in examples/
- only works for 3 ints of stdin

Bugs
- Will probably break if a newly discovered branch gets more input/does another read(2)
- possibly unnecessary deepcopies

'''

import sys
import Queue
import struct
import itertools
import re
import logging

sys.path.append('/home/ivan/Workspaces/manticore-ivan/manticore')
from manticore import Manticore
from manticore.core.plugin import ExtendedTracer, Follower, Plugin, ExamplePlugin
from manticore.core.smtlib.constraints import ConstraintSet
from manticore.core.smtlib import Z3Solver, solver
from manticore.core.smtlib.visitors  import pretty_print as pp

#from .state import Concretize, TerminateState

import copy
from manticore.core.smtlib.expression import *

#prog = '../linux/simpleassert'
prog = './hello'
main_end = 0x004004e0
VERBOSITY = 3

def _partition(pred, iterable):
    t1, t2 = itertools.tee(iterable)
    return (list(itertools.ifilterfalse(pred, t1)), filter(pred, t2))

def log(s):
    print '[+]', s

class TraceReceiver(Plugin):
    def __init__(self, tracer):
        self._trace = None
        self._tracer = tracer
        super(self.__class__, self).__init__()

    @property
    def trace(self):
        return self._trace

    def will_generate_testcase_callback(self, state, test_id, msg):
        self._trace = state.context[self._tracer.context_key]

        instructions, writes = _partition(lambda x: x['type'] == 'regs', self._trace)
        total = len(self._trace)
        log('Recorded concrete trace: {}/{} instructions, {}/{} writes'.format(
            len(instructions), total, len(writes), total))

logger = logging.getLogger(__name__)
class InstructionFollower(Plugin):

    def will_execute_instruction_callback(self, state, pc, instruction):
        #print("will_execute_instruction {} {} {}".format(state, hex(pc), instruction))
	if(pc==0x8000df00):
            raise TerminateState("Reached 0x8000df00, terminating.", testcase=False)


def flip(constraint):
    '''
    flips a constraint (Equal)

    (Equal (BitVecITE Cond IfC ElseC) IfC)
        ->
    (Equal (BitVecITE Cond IfC ElseC) ElseC)
    '''
    equal = copy.deepcopy(constraint)

    assert len(equal.operands) == 2
    # assume they are the equal -> ite form that we produce on standard branches
    ite, forcepc = equal.operands
    assert isinstance(ite, BitVecITE) and isinstance(forcepc, BitVecConstant)
    assert len(ite.operands) == 3
    cond, iifpc, eelsepc = ite.operands
    assert isinstance(iifpc, BitVecConstant) and isinstance(eelsepc, BitVecConstant)

    equal.operands[1] = eelsepc if forcepc.value == iifpc.value else iifpc

    return equal

def eq(a, b):
    # this ignores checking the conditions, only checks the 2 possible pcs
    # the one that it is forced to

    ite1, force1 = a.operands
    ite2, force2 = b.operands

    if force1.value != force2.value:
        return False

    _, first1, second1 = ite1.operands
    _, first2, second2 = ite1.operands

    if first1.value != first2.value:
        return False
    if second1.value != second2.value:
        return False

    return True

def perm(lst, func):
    ''' Produce permutations of `lst`, where permutations are mutated by `func`. Used for flipping constraints. highly
    possible that returned constraints can be unsat this does it blindly, without any attention to the constraints
    themselves

    Considering lst as a list of constraints, e.g.

      [ C1, C2, C3 ]

    we'd like to consider scenarios of all possible permutations of flipped constraints, excluding the original list.
    So we'd like to generate:

      [ func(C1),      C2 ,       C3 ],
      [      C1 , func(C2),       C3 ],
      [ func(C1), func(C2),       C3 ],
      [      C1 ,      C2 ,  func(C3)],
      .. etc

    This is effectively treating the list of constraints as a bitmask of width len(lst) and counting up, skipping the
    0th element (unmodified array).

    The code below yields lists of constraints permuted as above by treating list indeces as bitmasks from 1 to
     2**len(lst) and applying func to all the set bit offsets.

    '''
    for i in range(1, 2**len(lst)):
        yield [func(item) if (1<<j)&i else item for (j, item) in enumerate(lst)]

def constraints_to_constraintset(constupl):
    x = ConstraintSet()
    x._constraints = list(constupl)
    return x

def input_from_cons(constupl, datas):
    ' solve bytes in |datas| based on '
    newset = constraints_to_constraintset(constupl)

    ret = ''
    for data in datas:
        for c in data:
            ret += chr(solver.get_value(newset, c))
    return ret

# Run a concrete run with |inp| as stdin
def concrete_run_get_trace(inp):
    m1 = Manticore.linux(prog, concrete_start=inp, workspace_url='mem:')
    t = ExtendedTracer()
    r = TraceReceiver(t)
    m1.verbosity(VERBOSITY)
    m1.register_plugin(t)
    m1.register_plugin(r)
    m1.run(procs=1)
    return r.trace


def symbolic_run_get_cons(trace):
    '''
    Execute a symbolic run that follows a concrete run; return constraints generated
    and the stdin data produced
    '''

    m2 = Manticore.linux(prog, workspace_url='mem:')
    f = Follower(trace)
    m2.verbosity(VERBOSITY)
    m2.register_plugin(f)

    @m2.hook(main_end)
    def x(s):
        with m2.locked_context() as ctx:
            readdata = []
            for name, fd, data in s.platform.syscall_trace:
                if name in ('_receive', '_read') and fd == 0:
                    readdata.append(data)
            ctx['readdata'] = readdata
            ctx['constraints'] = list(s.constraints.constraints)

    m2.run()

    constraints = m2.context['constraints']
    datas = m2.context['readdata']

    return constraints, datas

def contains(new, olds):
    '__contains__ operator using the `eq` function'
    return any(eq(new, old) for old in olds)

def getnew(oldcons, newcons):
    "return all constraints in newcons that aren't in oldcons"
    return [new for new in newcons if not contains(new, oldcons)]

def constraints_are_sat(cons):
    'Whether constraints are sat'
    return solver.check(constraints_to_constraintset(cons))

def get_new_constrs_for_queue(oldcons, newcons):
    ret = []

    # i'm pretty sure its correct to assume newcons is a superset of oldcons

    new_constraints = getnew(oldcons, newcons)
    if not new_constraints:
        return ret

    perms = perm(new_constraints, flip)

    for p in perms:
        candidate = oldcons + p
        # candidate new constraint sets might not be sat because we blindly
        # permute the new constraints that the path uncovered and append them
        # back onto the original set. we do this without regard for how the
        # permutation of the new constraints combines with the old constratins
        # to affect the satisfiability of the whole
        if constraints_are_sat(candidate):
            ret.append(candidate)

    return ret

def inp2ints(inp):
    a, b, c = struct.unpack('<iii', inp)
    return 'a={} b={} c={}'.format(a, b, c)

def ints2inp(*ints):
    return struct.pack('<'+'i'*len(ints), *ints)

traces = set()
def concrete_input_to_constraints(ci, prev=None):
    global traces
    if prev is None:
        prev = []
    trc = concrete_run_get_trace(ci)

    # Only heed new traces
    trace_rips = tuple(x['values']['RIP'] for x in trc if x['type'] == 'regs')
    if trace_rips in traces:
        return [], []
    traces.add(trace_rips)
    
    log("getting constraints from symbolic run")
    cons, datas = symbolic_run_get_cons(trc)
    # hmmm ideally do some smart stuff so we don't have to check if the
    # constraints are unsat. something like the compare the constraints set
    # which you used to generate the input, and the constraint set you got
    # from the symex. sounds pretty hard
    #
    # but maybe a dumb way where we blindly permute the constraints
    # and just check if they're sat before queueing will work
    new_constraints = get_new_constrs_for_queue(prev, cons)
    log('permuting constraints and adding {} constraints sets to queue'.format(len(new_constraints)))
    return new_constraints, datas

# QMP and Mantcore use slighltl different register naming convention
# This function returns a mcore register name given a qmp register name,
# e.g. 'R00' -> 'R0' or 'd08' -> 'D8'
def qmpr2mcorer(regname):
    qmp_register_names_RX = ("R00", "R01","R02","R03","R04","R05","R06","R07","R08","R09","R10","R11","R12","R13","R14","R15")
    qmp_register_names_DX = ('d00', 'd01', 'd02', 'd03', 'd04', 'd05', 'd06', 'd07', 'd08',
                         'd09', 'd10', 'd11', 'd12', 'd13', 'd14', 'd15', 'd16',
                         'd17', 'd18', 'd19', 'd20', 'd21', 'd22', 'd23', 'd24',
                         'd25', 'd26', 'd27', 'd28', 'd29', 'd30', 'd31')
    mcore_register_names_RX = ("R0", "R1","R2","R3","R4","R5","R6","R7","R8","R9","R10","R11","R12","R13","R14","R15")
    mcore_register_names_DX = ('D0', 'D1', 'D2', 'D3', 'D4', 'D5', 'D6', 'D7', 'D8',
                         'D9', 'D10', 'D11', 'D12', 'D13', 'D14', 'D15', 'D16',
                         'D17', 'D18', 'D19', 'D20', 'D21', 'D22', 'D23', 'D24',
                         'D25', 'D26', 'D27', 'D28', 'D29', 'D30', 'D31')
    if regname in qmp_register_names_RX:
        return mcore_register_names_RX[qmp_register_names_RX.index(regname)]
    elif regname in qmp_register_names_DX:
        return mcore_register_names_DX[qmp_register_names_DX.index(regname)]
    else:
        return None


# Read file qmp-registers.txt in the current folder and
# update Manticore registers. Note that in Manticore we dont have
# s00-s63 registers
#
# @param m Manticore instance with an initial state to be updated
# @type class Manticore
def initialize_registers(state):
    filename = "qmp-registers.txt"
    try:
        f= open(filename,"r")
    except FileNotFoundError:
        print "[-] File ", filename, " does not exist!"
	return -1
    contents = f.read()

    # R01 -- R15
    register_names = ("R00", "R01","R02","R03","R04","R05","R06","R07","R08","R09","R10","R11","R12","R13","R14","R15")
    for regname in register_names:
        result = re.search("("+regname+")=([0-9a-f]{8})",contents)
	if result==None:
	    print "filename ", filename, " does not contains value for register ",regname,". Bug? We should abort!"
	    return -1
	mcore_regname = qmpr2mcorer(result.group(1))
	reg_value = result.group(2)
        print "Setting ",mcore_regname," --> ",reg_value
	state.cpu.regfile.write(mcore_regname, int(reg_value, 16))

    # D01 -- R31
    register_names = ('d00', 'd01', 'd02', 'd03', 'd04', 'd05', 'd06', 'd07', 'd08',
                         'd09', 'd10', 'd11', 'd12', 'd13', 'd14', 'd15', 'd16',
                         'd17', 'd18', 'd19', 'd20', 'd21', 'd22', 'd23', 'd24',
                         'd25', 'd26', 'd27', 'd28', 'd29', 'd30', 'd31')
    for regname in register_names:
        result = re.search("("+regname+")=([0-9a-f]{16})",contents)
	if result==None:
	    print "filename ", filename, " does not contains value for register ",regname,". Bug? We should abort!"
	    return -1
	mcore_regname = qmpr2mcorer(result.group(1))
	reg_value = result.group(2)
        print "Setting ",mcore_regname," --> ",reg_value
	state.cpu.regfile.write(mcore_regname, int(reg_value, 16))

def main():
    global main_end
    #m1 = Manticore.linux(prog, concrete_start=inp, workspace_url='mem:')
    #m1 = Manticore.linux(prog, concrete_start="abc", workspace_url='mem:')
    #m1 = Manticore.barebones(prog, concrete_start="abc", workspace_url='mem:')



    m1 = Manticore.barebones("img.elf")
    m1.verbosity(VERBOSITY)

    # Now let's read the registers
    print "[+] Reading registers"
    initialize_registers(m1.initial_state)

    #m1.initial_state.cpu.PC = 0x800df0c4
    #m1.initial_state.cpu.STACK = 0xbf9f7fa8  
    print "R15=",hex(m1.initial_state.cpu.R15)
    print "PC=",hex(m1.initial_state.cpu.PC)
    print "STACK=",hex(m1.initial_state.cpu.STACK)
    print "R13=",hex(m1.initial_state.cpu.R13)
    print "D24=",hex(m1.initial_state.cpu.D24)
    #exit(0)



    #m1._initial_state.cpu.PC = 0x00000000a0059050
    #print m1._initial_state.cpu
    #exit(0);
    # /* Register tracing plugins */
    #t = ExtendedTracer()
    #r = TraceReceiver(t)
    #m1.register_plugin(t)
    #m1.register_plugin(r)
    # NOTE: ./manticore/core/plugin.py:        state.cpu.RFLAGS = state.new_symbolic_value(state.cpu.address_bit_size)
    # NOTE: ./tests/test_state.py:138:         expr = self.state.new_symbolic_value(length)
    # NOTE: ./tests/test_unicorn.py:103:       self.mem.write(start, assemble(asm))

    #m1._initial_state.cpu.write_int(0x00601030, m1._initial_state.new_symbolic_value(8,label="myval"), size=8)
    #m1._initial_state.cpu.write_bytes(0x00601030, m1._initial_state.new_symbolic_value(8))
    #def write_int(self, where, expression, size=None, force=False):

    #m1.register_plugin(InstructionFollower())


    # Trigger an event when PC reaches a certain value
    end_address = 0x8000df00
    #end_address = 0x8000df00
    #end_address =  0x7f000070
    #end_address =  0x7f000034
    @m1.hook(end_address)
    def reached_goal(state):
        cpu = state.cpu
        assert cpu.PC == end_address
        #instruction = cpu.read_int(cpu.PC)
        print "Execution goal reached (pc={}). Terminating state".format(hex(end_address))
	#m1.terminate()
	state.abandon()
        #print "Instruction bytes: {:08x}".format(instruction)
        #print "0x{:016x}: {:08x}".format(cpu.PC,instruction)

    taint_id = 'taint_A'

    m1.initial_state.cpu.R1 = m1.initial_state.new_symbolic_value(32,taint=(taint_id,))
    print "R1=",m1.initial_state.cpu.R1
    #exit(0)
    m1.run(procs=1)
    exit(0);
    #return r.trace

    # Read the address of main's `ret` from cmdline if we're passed it. Used for testing.
    if len(sys.argv) > 1:
        main_end = int(sys.argv[1], 0)
        log("Got end of main: {:x}".format(main_end))

    q = Queue.Queue()

    # todo randomly generated concrete start
    stdin = ints2inp(0, 5, 0)

    log('seed input generated ({}), running initial concrete run.'.format(inp2ints(stdin)))

    to_queue, datas = concrete_input_to_constraints(stdin)
    for each in to_queue:
        q.put(each)

    # hmmm probably issues with the datas stuff here? probably need to store
    # the datas in the q or something. what if there was a new read(2) deep in the program, changing the datas
    while not q.empty():
        log('get constraint set from queue, queue size: {}'.format(q.qsize()))
        cons = q.get()
        inp = input_from_cons(cons, datas)
        to_queue, new_datas = concrete_input_to_constraints(inp, cons)
        if len(new_datas) > 0:
            datas = new_datas

        for each in to_queue:
            q.put(each)

    log('paths found: {}'.format(len(traces)))


    

if __name__=='__main__':
    main()
