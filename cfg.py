#coding=utf-8

from capstone import *
from capstone.arm64 import *
from graphviz import Digraph
from unicorn import *
from unicorn.arm64_const import *
from keystone import *


def reg_ctou(regname):#
    # This function covert capstone reg name to unicorn reg const.
    type1 = regname[0]
    if type1 == 'w' or type1 =='x':
        idx = int(regname[1:])
        if type1 == 'w':
            return idx + UC_ARM64_REG_W0
        else:
            if idx == 29:
                return  1
            elif idx == 30:
                return 2
            else:
                return idx + UC_ARM64_REG_X0
    elif regname=='sp':
        return 4
    return None

def asm_no_branch(ori,dist):
    ks = Ks(KS_ARCH_ARM64, KS_MODE_LITTLE_ENDIAN)
    print ("b #0x%x" % dist)
    ins, count  = ks.asm(("b #0x%x" % dist),ori)
    return  ins

def asm_has_branch(ori,dist1,dist2,cond):
    ks = Ks(KS_ARCH_ARM64, KS_MODE_LITTLE_ENDIAN)
    if ori == 0xb73b4:
        pass
    print "b%s #0x%x;b #0x%x" % (cond,dist1,dist2)
    ins, count = ks.asm("b%s #0x%x;b #0x%x" % (cond,dist1,dist2),ori)
    return ins

# callback for tracing instructions
def hook_code(uc, address, size, user_data):
    global real_blocks
    global csel_addrs
    global list_trace
    global startaddr
    global debugflag
    global isSucess
    global distAddr
    global branch_control
    global list_blocks
    ban_ins = ["bl"]

    if isSucess:
        mu.emu_stop()
        #raw_input()
        return

    if address > end:
        uc.emu_stop()
        return

    for ins in md.disasm(bin1[address:address+size],address):
        print(">>> Tracing instruction at 0x%x, instruction size = 0x%x" % (address, size))
        print(">>> 0x%x:\t%s\t%s" % (ins.address, ins.mnemonic, ins.op_str))
        print

        if address in real_blocks:
            if list_trace.has_key(address):
                print "sssssss"
                ch = raw_input("This maybe a fake block. codesign:%s " % get_code_sign(list_blocks[address]))

                uc.emu_stop()
            else:
                list_trace[address] = 1

        if address in real_blocks and address != startaddr:
            isSucess = True
            distAddr = address
            print 'find:%x' % address
            uc.emu_stop()
            return
        
        #是否跳过指令
        flag_pass = False
        for b in ban_ins:
            if ins.mnemonic.find(b) != -1:
                flag_pass = True
                break
            
        #只允许对栈的操作
        if ins.op_str.find('[') != -1:
            if ins.op_str.find('[sp') == -1:
                flag_pass = True
                for op in ins.operands:
                    if op.type == ARM64_OP_MEM:
                        addr = 0
                        if op.value.mem.base != 0:
                            addr += mu.reg_read(reg_ctou(ins.reg_name(op.value.mem.base)))
                        elif op.value.index != 0:
                            addr += mu.reg_read(reg_ctou(ins.reg_name(op.value.mem.index)))
                        elif op.value.disp != 0:
                            addr += op.value.disp
                        if addr >= 0x80000000 and addr < 0x80000000 +  0x10000 * 8:
                            flag_pass = False
        if flag_pass:
            print("will pass 0x%x:\t%s\t%s" %(ins.address, ins.mnemonic, ins.op_str))
            uc.reg_write(UC_ARM64_REG_PC, address + size)
            return
        
        
        #breaks 0x31300
        if address in [ 0xB72EC ] or debugflag:
            debugflag = True
            print("0x%x:\t%s\t%s" % (ins.address, ins.mnemonic, ins.op_str))
            while True:
                c = raw_input('>')
                if c == '':
                    break
                if c == 's':
                    uc.emu_stop()
                    return
                if c == 'r':
                    debugflag = False
                    break
                if c[0] == '!':
                    reg = reg_ctou(c[1:])
                    print "%s=%x (%d)" % (c[1:], mu.reg_read(reg),mu.reg_read(reg))
                    continue

        if ins.mnemonic == 'ret':
            uc.reg_write(UC_ARM64_REG_PC, 0)
            isSucess = False
            print "ret ins.."
            mu.emu_stop()

        #ollvm branch
        if ins.mnemonic == 'csel':
            print("csel 0x%x:\t%s\t%s" %(ins.address, ins.mnemonic, ins.op_str))
            regs = [reg_ctou(x) for x in ins.op_str.split(', ')]
            assert len(regs) == 4
            v1 = uc.reg_read(regs[1])
            v2 = uc.reg_read(regs[2])
            if branch_control == 1:
                uc.reg_write(regs[0],v1)
            else:
                uc.reg_write(regs[0],v2)
            uc.reg_write(UC_ARM64_REG_PC, address + size)

# callback for memory exception
def hook_mem_access(uc,type,address,size,value,userdata):
    pc = uc.reg_read(UC_ARM64_REG_PC)
    print 'pc:%x type:%d addr:%x size:%x' % (pc,type,address,size)
    #uc.emu_stop()
    return False


def get_code_sign(block):
    insn = block['capstone']
    sign = ''
    for i in insn:
        sign += i.mnemonic
        for op in i.operands:
            sign += str(op.type)
    return sign

def get_context():
    global mu
    regs = []
    for i in range(31):
        idx = UC_ARM64_REG_X0 + i
        regs.append(mu.reg_read(idx))
    regs.append(mu.reg_read(UC_ARM64_REG_SP))
    return regs

def set_context(regs):
    global mu
    if regs == None:
        return
    for i in range(31):
        idx = UC_ARM64_REG_X0 + i
        mu.reg_write(idx,regs[i])
    mu.reg_write(UC_ARM64_REG_SP,regs[31])

def find_path(start_addr,branch = None):
    global real_blocks
    global bin1
    global mu
    global list_trace
    global startaddr
    global distAddr
    global isSucess
    global branch_control
    try:
        list_trace = {}
        startaddr = start_addr
        isSucess = False
        distAddr = 0
        branch_control = branch
        mu.emu_start(start_addr,0x10000)
        print "emu end.."

    except UcError as e:
        pc = mu.reg_read(UC_ARM64_REG_PC)
        print ("111 pc:%x" % pc)
        if pc != 0:
            #mu.reg_write(UC_ARM64_REG_PC, pc + 4)
            return find_path(pc + 4,branch)
        else:
            print("ERROR: %s  pc:%x" % (e,pc))
    if isSucess:
        return distAddr
    return None
	
ssign = {u'b2',
 u'cmp11b.ne2',
 u'cmp11mov11b.ne2',
 u'movz12movk12b2',
 u'movz12movk12cmp11b.ne2',
 u'movz12movk12cmp11mov11b.ne2',
 'movz12movk12cmp11mov11movz12movk12movz12movk12b.ne2',
 u'movz12movk12cmp11movz12movk12b.eq2',
 'movz12movk12cmp11movz12movk12b.ne2',
 'movz12movk12movz12movk12b2',
 'movz12movk12cmp11movz12movk12movz12movk12movz12movk12b.eq2',
 'movz12movk12movz12movk12cmp11b.eq2',
 'movz12movk12movz12movk12cmp11movz12movk12b.eq2',
 'movz12movk12cmp11b.eq2',
 'ldr13b2',
 'mov11movz12movk12cmp11movz12movk12b.eq2'
 }
ssign2 = set()
def  is_real_blocks(ins):
    sign = get_code_sign(ins)
    if sign in ssign:
        return False
    if sign.endswith('movk12movz12movk12b.ne2'):
        return False

    for insn in item['capstone']:
        #print insn.mnemonic
        if insn.mnemonic not in ['movz','movk','cmp','b.eq','b.ne']:
            return True
    ssign2.add(sign)
    return False

def draw():
    queue = []
    dot = Digraph(comment='The Round Table')
    dot.attr('node', shape='box')
    queue.append(offset)
    check = {}
    while len(queue) > 0:
        pc = queue.pop()
        if check.has_key(pc):
            continue
        check[pc] = 1
        dot.node(hex(pc),list_blocks[pc]['ins'])
        for i in flow[pc]:
            if i != None:
                dot.edge(hex(pc), hex(i), constraint='true')
                queue.append(i)
    dot.render('test-output/round-table.gv', view=True)
    
def fix(bin):
    queue.append(offset)
    check = {}
    while len(queue) > 0:
        pc = queue.pop()
        if check.has_key(pc):
            continue
        check[pc] = 1

        if(len(flow[pc]) == 2):
            insn = list_blocks[pc]["capstone"][-2]
            patch_offset = list_blocks[pc]["eaddress"] - 4
            if insn.mnemonic == 'csel':    
                opcode = asm_has_branch(patch_offset, flow[pc][0], flow[pc][1], insn.op_str[-2:])      
                op_str = "".join([ chr(i) for i in opcode ])
                bin = bin[:patch_offset] + op_str + bin[patch_offset+8:]
            else:
                print "error !!!!!!"
                raw_input()
                
        if(len(flow[pc]) == 1):
            patch_offset = list_blocks[pc]["eaddress"]
            opcode = asm_no_branch(patch_offset, flow[pc][0])
            op_str = "".join([ chr(i) for i in opcode ])
            bin = bin[:patch_offset] + op_str + bin[patch_offset+4:]
        
        if(len(flow[pc]) == 0):
            #ret block
            continue
            
        for i in flow[pc]:
            if i != None:
                queue.append(i)
                
    with open("libvdog.new.so","wb") as fp:
        fp.write(bin)

def print_real_blocks():
    print '######################### real blocks ###########################'
    cnt = 0
    for i in real_blocks:
        item = list_blocks[i]
        print item['ins']
        print
        if cnt == 50:
            c = raw_input()
            if c == 'c':
                return
        cnt += 1

		
offset = 0x70438 #function start
end = 0x7170C    #function end

bin1 = open('libvdog.so','rb').read()
md = Cs(CS_ARCH_ARM64,CS_MODE_ARM)
md.detail = True #enable detail analyise

list_blocks = {}
block_item = {}
processors = {}
dead_loop = []
real_blocks = []
csel_list_cond = {}
    

isNew = True
insStr = ''
for i in md.disasm(bin1[offset:end],offset):
    insStr += "0x%x:\t%s\t%s\n" %(i.address, i.mnemonic, i.op_str) 
    if isNew:
        isNew = False
        block_item = {}
        block_item["saddress"] = i.address
        block_item['capstone'] = []

    block_item['capstone'].append(i)
    block_item['flag'] = False

    if len(i.groups) > 0 or i.mnemonic == 'ret':
        isNew = True
        block_item["eaddress"] = i.address
        block_item['ins'] = insStr
        
        for op in i.operands:
            if op.type == ARM64_OP_IMM:
                block_item["naddress"] = op.value.imm

                if op.value.imm == i.address:
                    print "dead loop:%x" % i.address
                    dead_loop.append(i.address)

                if not processors.has_key(op.value.imm):
                    processors[op.value.imm] = 1
                else:
                    processors[op.value.imm] += 1
        if not block_item.has_key("naddress"):
            block_item['naddress'] = None
        list_blocks[block_item["saddress"]] = block_item
        
        insStr = ''

#delete dead loop
for dead in dead_loop:
    if processors.has_key(dead):
        del(processors[dead])

for b in list_blocks:
    if processors.has_key(list_blocks[b]['naddress']):
        if processors[list_blocks[b]['naddress']] > 1:
            real_blocks.append(list_blocks[b]['saddress'])

fake_blocks = []
for i in real_blocks:
    item = list_blocks[i]
    if not is_real_blocks(item):
        print '## fake block ###'
        print item['ins']
        fake_blocks.append(i)

for x in fake_blocks:
    real_blocks.remove(x)

for i in list_blocks:
    if list_blocks[i]['ins'].find('ret') != -1:
        print 'ret block:%x' % i
        real_blocks.append(i)

print '######################### real blocks ###########################'
print [hex(x) for x in real_blocks]

#Initialize emulator in ARM64 mode
mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)

#init stack
mu.mem_map(0x80000000,0x10000 * 8)

# map 4MB memory for this emulation
mu.mem_map(0, 4 * 1024 * 1024)

# write machine code to be emulated to memory
mu.mem_write(0, bin1)
mu.reg_write(UC_ARM64_REG_SP, 0x80000000 + 0x10000 * 6)
mu.hook_add(UC_HOOK_CODE, hook_code)
mu.hook_add(UC_HOOK_MEM_UNMAPPED, hook_mem_access)

list_trace = {}
debugflag = False

if offset in real_blocks:
    real_blocks.remove(offset)

queue = [(offset,None)]
flow = {}

while len(queue) != 0:
    env = queue.pop()
    pc = env[0]
    set_context(env[1])
    item = list_blocks[pc]
    if pc in flow:
        #print "???"
        continue
    flow[pc] = []
    
    #代码块中有ollvm生成的分支
    if item['ins'].find('csel') != -1:
        #raw_input()
        ctx = get_context()
        p1 = find_path(pc,0)
        if p1 != None:
            queue.append((p1,get_context()))
            flow[pc].append(p1)

        set_context(ctx)
        p2 = find_path(pc,1)

        if p1 == p2:
            p2 = None

        if p2 != None:
            queue.append((p2,get_context()))
            flow[pc].append(p2)
    else:
        p = find_path(pc)
        if p != None:
            queue.append((p,get_context()))
            flow[pc].append(p)
draw()
fix(bin1)

