import pprint
import json
import sys
import copy
from dict_insnref import instr_ref,sml_correspondence
from to_sml import to_sml
from collections import ChainMap
import string
import random

pp = pprint.PrettyPrinter(indent=4)

def generate_random_name(length=10):
    # Generate a random string of letters
    return ''.join(random.choices(string.ascii_letters, k=length))


def is_equal_ignore_order(list1, list2):
    if len(list1) != len(list2):
        return False
    unmatched_list2 = list2.copy()
    for elem1 in list1:
        found_match = False
        for i, elem2 in enumerate(unmatched_list2):
            if elem1 == elem2:
                found_match = True
                unmatched_list2.pop(i)
                break
        if not found_match:
            return False

    return True

def debug_filter(x, y):
    print("Debug - x:", x)  # Print the content of x
    print("Debug - y:", y)  # Print the content of y
    if "dest" not in x:
        raise KeyError("'dest' key is missing in x")
    result = [item for item in y if x["dest"] not in item[-1]] + [(x["dest"], x["position"])]
    print("Debug - result:", result)
    return result

def do_union(lst):
    lst1 = lst.copy()
    result = []
    for sublist in lst:
        for item in sublist:
            if item not in result:
               result.append(item)
    return result



def do_intersection(lst):
    lst1 = lst.copy()
    intersection = []
    if [] in lst1:
        return []
    if len(lst1) == 1:
        return lst1[0]
    intersection = lst1[0]
    for sublist in lst1[1:]:
        intersection = [item for item in intersection if item in sublist]
    return intersection


class create_cfg:
    def __init__(self, bril_func):
        self.bril_func = bril_func
        self.cfg = self.form_cfg()

    def form_cfg(self):
        Terminators = ["jmp","br","ret"]
        function = self.bril_func
        basic_blocks = []
        instructions = function["instrs"]
        basic_block = []
        for insn_pos,instruction in enumerate(instructions):
            #print(instruction)
            if("label" in instruction.keys()):
                if(basic_block != []):
                    basic_blocks.append(basic_block)
                basic_block = list()
                basic_block.append(instruction)

            elif(instruction["op"] in Terminators):
                basic_block.append(instruction)
                basic_blocks.append(basic_block)
                basic_block = list()
            else:
                basic_block.append(instruction)
        if(basic_block != []):
            basic_blocks.append(basic_block)

        for blk in basic_blocks:
            print("dblk",blk)
            if("label" not in blk[0]):
               name = generate_random_name()
               print(blk)
               blk.insert(0,{"label":name})
        name = generate_random_name()
        ins_tr = instr_ref["jmp"]
        print("creating entry",name,basic_blocks[0][0])
        ins_tr["labels"] = [basic_blocks[0][0]["label"]]
        basic_blocks.insert(0,[{"label":name},ins_tr])
        #print("bbs",basic_blocks)
        print("creating entry",name,basic_blocks[0])
        cfg = self.populate_cfg_edges(basic_blocks)
        return cfg

    def populate_cfg_edges(self,basic_blocks):
        cfg = []
        num_of_basic_blocks = len(basic_blocks)
        label_to_blocknum = {}
        for block_num,block in enumerate(basic_blocks):
            if("label" in block[0]):
                label_to_blocknum.update({block[0]["label"]:block_num})
        for block_num,block in enumerate(basic_blocks):
            print("----------",block,"\nBBS\n",basic_blocks,"\n>>>>>>>>>>>>>>>>>>>")
            if("op" in block[-1] and block[-1]["op"] in ["jmp","br"]):
                vals = [label_to_blocknum[key] for key in block[-1]["labels"]]
                cfg.append([block,vals])
                print("taken 1",basic_blocks)
            elif("op" in block[-1] and block[-1]["op"] == "ret"):
                cfg.append([block,[-1]])
                print("taken 2",basic_blocks)
            else:
                if(block_num == num_of_basic_blocks-1):
                   cfg.append([block,[-1]])
                else:
                   print("APPPPPPPPPPPPPPPPPPPPPPENDING JMPPPPPPPPPPPPPPPPPPPPPPPPPPPPP")
                   ins_tr = copy.deepcopy(instr_ref["jmp"])
                   if ("label" in basic_blocks[block_num+1][0]):
                      #print("---------",block)
                      ins_tr["labels"] = [basic_blocks[block_num+1][0]["label"]]
                      block.append(ins_tr)
                      print(basic_blocks)
                   cfg.append([block,[block_num+1]])
            print("EXIT ----------",basic_blocks)
        print("CFG",cfg)
        return cfg


class optimize_ir:
    def __init__(self, bril_func):
        self.bril_func = copy.deepcopy(bril_func)
        self.copy_func = copy.deepcopy(bril_func)
        self.func_args = [name["name"] for name in bril_func["args"]] if "args" in bril_func else []
        self.cfg = self.bril_func["cfg"]
        self.blocks = [block[0] for block in self.cfg]
        #self.apply_local_optimizations(self.blocks)
        print("test",self.cfg)
        self.dfa_impl_std_analysis(self.cfg)
        self.populate_with_dominance_info(self.regular_analysis)
        self.to_ssa(self.dom_info)

    def apply_local_optimizations(self, blocks):
        blocks = self.blocks
        self.lvn_blocks= [self.sl_vn(block,False) for block in blocks]
        if(len(blocks)==1):
          self.lvn_blocks = [self.sl_dce(block,True) for block in self.lvn_blocks]
        else:
          self.lvn_blocks = [self.sl_dce(block,False) for block in self.lvn_blocks]

    def sl_dce(self, block,eager):
        num_cfg_blocks = len(self.cfg)
        old_block = block
        optimized_block = []
        while(old_block != optimized_block):
                 #we store tracking like where its defined and where its used
                 #each element in use_def_mapping is of the form "var_name":{"defines":[],"uses":[]}
                 use_def_mapping = {}
                 #instructions that can be deleted at the end of each run
                 mark_for_delete = set()
                 for position,instruction in enumerate(old_block):
                     #obtain destination and args
                     destination = [instruction["dest"]] if "dest" in instruction else []
                     uses = instruction["args"] if "args" in instruction else []
                     for use in uses:
                         #if this arg is not in mapping its either a func arg or something from previous block
                         if(use not in use_def_mapping):
                            use_def_mapping.update({use:{"defines":[],"uses":[position]}})
                         else:
                            #update with usage information
                            #previous usage is overwritten because its of no use
                            use_def_mapping[use]["uses"] = [position]
                     for dest in destination:
                         #if this destination not in mapping its a definition
                         if(dest not in use_def_mapping):
                            use_def_mapping.update({dest:{"defines":[position],"uses":[]}})
                         #destinantion in mapping check for redefines which have not been previously been used
                         elif(use_def_mapping[dest]["uses"] == []):
                              #print(use_def_mapping[dest]["defines"])
                              mark_for_delete.update(use_def_mapping[dest]["defines"])
                              #reset
                              use_def_mapping[dest]["defines"] = [position]
                         else:
                              use_def_mapping[dest]["defines"] = [position]
                              use_def_mapping[dest]["uses"] = []
                 if eager:
                    #we do eager only if there is one block, delete insn that arent used at all
                    for variable_info in use_def_mapping:
                        #print(use_def_mapping)
                        if(use_def_mapping[variable_info]["uses"] == []):
                           mark_for_delete.update(use_def_mapping[variable_info]["defines"])
                 optimized_block = [instruction for instruction_postion,instruction in enumerate(old_block) if instruction_postion not in mark_for_delete ]
                 #exchange blocks terminates when blocks dont change
                 old_block,optimized_block = optimized_block,old_block
        return old_block

    def sl_vn(self, block,do_fold):
        #environment mappin to keep track for current variable
        env = {}
        #main lvn datastructure
        lvn_tbl = [] #each entry {"expression":{"op":,op_field:[]},"canonical_home":{}}
        #list of reconstructed instructions
        new_block = []
        for insn_pos,instruction in enumerate(block):
            #all binary operations
            binary_operations = {"add","sub","div","mul","eq","lt","gt","le","ge","and","or"}
            #operations that are commutative to perform commutative cse
            #"lt","gt","le","ge" are commutative provided operator is compared with its opposites
            commutative_operations = binary_operations - {"sub","div"}
            #operations that can be folded
            foldable_operations = binary_operations
            foldable_operations.update({"not"})
            #effect operations shouldnt be involved in lvn
            effect_op = {"jmp","br","call","ret"}
            #operations for which cse needs to be skipped
            skip_cse = effect_op
            skip_cse.update({"const","print","nop","id"})
            #obtain op args and dest fields
            op = instruction["op"] if "op" in instruction else None
            args = instruction["args"] if "args" in instruction else []
            args = [instruction["value"]] if instruction.get("op") == "const" else args
            destinations = [instruction["dest"]] if "dest" in instruction else []
            table_positions = []
            canonical_home = None
            #for each argument update its poition from table
            for arg in args:
                if(arg in env and op != "const"):
                   table_positions.append(env[arg])
                else:
                   table_positions.append(arg)
            #rename variable
            for other_dest_num in range(insn_pos + 1, len(block)):
                other_inst = block[other_dest_num]
                if('dest' in instruction and  'dest' in other_inst and instruction['dest'] == other_inst['dest']):
                       canonical_home = instruction['dest']+str(insn_pos)
                       break
            for dest in destinations:
                if(canonical_home == None):
                   canonical_home = destinations[0]
            #copy propagation
            for pos,table_position in enumerate(table_positions):
                if(type(table_position) == int):
                   if(op != 'const' and lvn_tbl[table_position]["expression"]["op"] == "id"):
                      if(type(lvn_tbl[table_position]["expression"]["op_field"][0]) == int or lvn_tbl[table_position]["expression"]["op_field"][0] not in env):
                         table_positions[pos] = lvn_tbl[table_position]["expression"]["op_field"][0]
            if op == "ge":
               updated_op = "lt"
            elif op == "le":
               updated_op = "gt"
            elif op == "lt":
               updated_op = "ge"
            elif op == "gt":
               updated_op = "le"
            else:
               updated_op = op
            rev_tbl= copy.deepcopy(table_positions)
            rev_tbl.reverse()
            cse_targ = {"op":op,"op_field":table_positions}
            reverse_cse_targ = {"op":updated_op,"op_field":rev_tbl}
            if(op=="const"):
               env[dest] = len(lvn_tbl)
               lvn_tbl.append({"expression":cse_targ,"canonical_home":canonical_home})
               instruction["dest"] = canonical_home
               new_block.append(instruction)
               continue
            found = False
            #do a cse(subexpr elimination) ignore if cse is not valid
            #check for matching expression in table or matching expression with positions reversed if
            #operation is commutative
            for entry_pos,entry in enumerate(lvn_tbl):
                if(op in skip_cse):
                      break;
                elif(cse_targ == entry["expression"] or (op in commutative_operations and reverse_cse_targ == entry["expression"])):
                      found = True;
                      break;
            #

            #fold only if its enabled and operator is foldable
            if(do_fold and op in foldable_operations and all(lvn_tbl[pos]["expression"]["op"] == "const" for pos in table_positions)):
               constants = [lvn_tbl[pos]["expression"]["op_field"][0] for pos in table_positions]
               result = self.interpret(instruction,constants)
               if(result != None):
                  env[instruction["dest"]] = len(lvn_tbl)
                  lvn_tbl.append({"expression":{"op":"const","op_field":[result["value"]]},"canonical_home":canonical_home})
                  result["dest"] = canonical_home
                  new_block.append(result)
                  continue

            insn = copy.deepcopy(instruction)
            canon_args = [lvn_tbl[arg]["canonical_home"] if isinstance(arg, int) else arg for arg in table_positions]
            if "args" in insn:
                     insn["args"] = canon_args
            if "dest" in insn:
                     insn["dest"] = canonical_home
            if(found):
               env[dest] = entry_pos
               #lvn_tbl.append({"expression":{"op":id,"op_field":[entry_pos]},"canonical_home":canonical_home})
               new_insn = copy.deepcopy(instr_ref["id"])
               new_insn["args"] = [lvn_tbl[entry_pos]["canonical_home"]]
               new_insn["dest"] = canonical_home
               new_block.append(new_insn)
            else:
               if(op in skip_cse and "dest" in insn):
                  env[dest] = len(lvn_tbl)
                  lvn_tbl.append({"expression":cse_targ,"canonical_home":canonical_home})
                  new_block.append(insn)
               elif('dest' not in instruction):
                  new_block.append(insn)
               else:
                  env[dest] = len(lvn_tbl)
                  lvn_tbl.append({"expression":cse_targ,"canonical_home":canonical_home})
                  new_block.append(insn)
        return new_block


    def interpret(self, instruction,ref_from_tbl):
         op = instruction["op"]
         inst = copy.deepcopy(instr_ref["const_int"])
         bool_inst = copy.deepcopy(instr_ref["const_bool"])
         bool_inst["dest"] = instruction["dest"]
         inst["dest"] = instruction["dest"]
         if(op == "id"):
            if(instruction["type"] == "bool"):
               bool_inst["value"] = [ref_from_tbl[0]]
               return bool_inst
            else:
               inst["value"] = [ref_from_tbl[0]]
               return inst

         result = None
         if op == "add":
            result = ref_from_tbl[0] + ref_from_tbl[1]
         elif op == "mul":
            result = ref_from_tbl[0] * ref_from_tbl[1]
         elif op == "sub":
            result = ref_from_tbl[0] - ref_from_tbl[1]
         elif op == "div":
              if ref_from_tbl[1] != 0:
                 result = ref_from_tbl[0] / ref_from_tbl[1]
              else:
                 return None
         if(result!=None):
            inst["value"] = result
            return inst
         if op == "and":
            result = ref_from_tbl[0] and ref_from_tbl[1]
         elif op == "or":
            result = ref_from_tbl[0] or ref_from_tbl[1]
         elif op == "not":
            result = not ref_from_tbl[0]
         elif op == "lt":
            result = ref_from_tbl[0] < ref_from_tbl[1]
         elif op == "gt":
            result = ref_from_tbl[0] > ref_from_tbl[1]
         elif op == "le":
            result = ref_from_tbl[0] <= ref_from_tbl[1]
         elif op == "ge":
            result = ref_from_tbl[0] >= ref_from_tbl[1]
         if(result!=None):
            bool_inst["value"] = result
            return bool_inst

    def print_analysis(self,analysis,tag):
        #print(analysis)
        print("--------------",tag,"---------------------")
        for key, sub_dict in analysis.items():
            print()
            print(sub_dict[0][0],"-->",key," : ",sub_dict[1]["meta"][tag][0])
            print("###################################################")
            print(sub_dict[0][-1],"-->",key," : ",sub_dict[1]["meta"][tag][-1])
            print()
        print("--------------------------------------")

    def print_instrs(self,analysis):
        for key, sub_dict in analysis.items():
            print(sub_dict[0])

    def print_orig(self,data,tosml,tree):
        result = []
        if(tosml):
           to_sml(self.copy_func,data,tree)
        for key, value in data.items():
            list_of_dicts = value[0]
            for sub_dict in list_of_dicts:
                if 'position' in sub_dict:
                    del sub_dict['position']
                result.append(sub_dict)
        bfunc = copy.deepcopy(self.copy_func)
        bfunc["instrs"] = result
        del bfunc["cfg"]
        x = {}
        x["functions"] = [bfunc]
        if(not tosml):
           print(str(json.dumps(x)))

    def dfa_impl_std_analysis(self,blocks):
        print("ye dfa")
        print(blocks)
        copy_cfg = copy.deepcopy(blocks)
        universal_expr_set = []
        #preprocess with meta data
        for bl_num,block in enumerate(copy_cfg):
                   sucessors = block.pop(1)
                   if sucessors == [-1] : sucessors = []
                   meta = {"meta":{"suc":sucessors,"pred":[]}}
                   block.append(meta)
                   copy_cfg[bl_num] = {bl_num:block}

        for bl_num,i in enumerate(copy_cfg):
            succs = i[bl_num][1]["meta"]["suc"]
            for sucs in succs:
                copy_cfg[sucs][sucs][1]["meta"]["pred"].append(bl_num)
            for index,j in enumerate(i[bl_num][0]):
                  j["position"] = str(bl_num)+"_"+str(index)
                  expr_set = ()
                  if 'args' in j and 'op' in j:
                      expr_set = (j['op'],j['args'])
                  if expr_set != () and expr_set not in universal_expr_set:
                      universal_expr_set.append(expr_set)

        dict_ = {}
        for bl_num,i in enumerate(copy_cfg):
             dict_.update(i)
        print("stuck")
        #reaching_definitions
        def reaching_transfer(instr,currentmeta):
            currentmeta1 = currentmeta.copy()
            if "dest" not in instr:
               return currentmeta1
            new_elem = (instr["dest"], instr["position"])
            updated_meta = [elem for elem in currentmeta1 if elem[0] != instr["dest"]]
            updated_meta.append(new_elem)
            return updated_meta

        analysis = self.dfa_do_work_list(True,dict_,[],[],do_union,reaching_transfer,"reachingdefs",[],[])
        #self.print_analysis(analysis,"reachingdefs")
        #self.univ_expr_set = universal_expr_set
        #print(":(")
        #liveness analysis
        def liveness_transfer(instr, currentmeta):
            currentmeta1 = currentmeta.copy()
            if "dest" in instr:
               currentmeta1 = [elem for elem in currentmeta if elem != instr["dest"]]
            if "args" in instr:
               currentmeta1 = do_union([currentmeta1, instr["args"]])
            return currentmeta1

        analysis = self.dfa_do_work_list(False,analysis,[],[],do_union,liveness_transfer,"liveness",[],[])
        #self.print_analysis(analysis,"liveness")
        #print("junknk")
        #available exrs
        def available_transfer(instr, currentmeta):
            currentmeta1 = currentmeta.copy()
            if "op" not in instr or "args" not in instr:
               return currentmeta1
            new_tuple = (instr["op"], instr["args"])
            currentmeta1.append(new_tuple)
            new_currentmeta = []
            if "dest" in instr:
               for elem in currentmeta1:
                   if instr["dest"] not in elem[1]:
                      new_currentmeta.append(elem)
            return new_currentmeta

        analysis = self.dfa_do_work_list(True,analysis,[],universal_expr_set,do_intersection,available_transfer,"availableexpr",[],[])
        #self.print_analysis(analysis,"availableexpr")
        print("ae")
        #very busy expression
        def verybusy_transfer(instr, currentmeta):
            cu = currentmeta.copy()
            if "op" not in instr or "args" not in instr:
               return cu
            new_tuple = (instr["op"], instr["args"])
            if "dest" in instr:
               cu = [elem for elem in currentmeta if instr["dest"] not in elem[1]]
            cu.append(new_tuple)
            return cu

        #analysis = self.dfa_do_work_list(False,analysis,universal_expr_set,[],do_intersection,verybusy_transfer,"vbusyexpr",[],[])
        #self.print_analysis(analysis,"vbusyexpr")
        self.regular_analysis = analysis
        print("end")

    def dfa_do_work_list(self,isForward,cfg,ininit,outinit,merge,transfer,tag,dummyinini,dummyoutini):
        #we take a granular approach and do it insn by insn

        if(isForward):
           cfg_len = len(cfg)
           dummy = {cfg_len:[[],{'meta': {'suc': [0], 'pred': [],tag:[{"in":dummyinini,"out":dummyoutini}]}}]}
           cfg.update(dummy)
           cfg[0][1]["meta"]["pred"].append(cfg_len)
        else:
           cfg_len = len(cfg)
           dummy = {cfg_len:[[],{'meta': {'suc': [], 'pred': [],tag:[{"in":dummyinini,"out":dummyoutini}]}}]}
           for key, sub_dict in cfg.items():
               if(sub_dict[1]["meta"]["suc"] == []):
                  sub_dict[1]["meta"]["suc"].append(cfg_len)
                  dummy[cfg_len][1]["meta"]["pred"].append(key)
           cfg.update(dummy)

        for key, sub_dict in cfg.items():
            cfg_len = len(cfg)-1
            if(key == cfg_len): continue
            sub_dict[1]["meta"][tag] = [{"in":ininit,"out":outinit}]

        copy_cfg = copy.deepcopy(cfg)
        work_list = list(cfg.keys())

        i = 0
        while i < len(work_list):
              key = work_list.pop(0)
              block = copy.deepcopy(cfg.pop(key))
              istrs = block[0]
              succ = block[1]["meta"]["suc"]
              pred = block[1]["meta"]["pred"]
              analysis = []
              ref_per_insn = {"in":None,"out":None}
              if(isForward):
                     merge_to = "in"
                     tranfer_on = "out"
                     collect_items = pred
                     collect_pos = -1
                     check_for = succ
              if(not isForward):
                     istrs.reverse()
                     merge_to = "out"
                     tranfer_on = "in"
                     collect_items = succ
                     collect_pos = 0
                     check_for = pred
              for instr_pos,instr in enumerate(istrs):
                  calc = copy.deepcopy(ref_per_insn)
                  if(instr_pos == 0):
                     collection = []
                     for collected_item in collect_items:
                         collection.append(copy_cfg[collected_item][1]["meta"][tag][collect_pos][tranfer_on])
                  else:
                     collection = [analysis[-1][tranfer_on]]
                  calc[merge_to]  = merge(collection)
                  calc[tranfer_on] = transfer(instr,calc[merge_to])
                  analysis.append(calc)
                  if(instr_pos == len(istrs)-1):
                      if(not isForward):
                          analysis.reverse()
                      copy_cfg[key][1]["meta"][tag] = analysis
                      cfg[key]= copy_cfg[key]
                      if(not (is_equal_ignore_order(block[1]["meta"][tag][collect_pos]["in"], calc["in"]) and is_equal_ignore_order(block[1]["meta"][tag][collect_pos]["out"], calc["out"]))):
                          for check in check_for:
                              if check not in work_list:
                                 work_list.append(check)
                      analysis = []
                  continue
              cfg[key]= copy_cfg[key]

        keylen = len(copy_cfg) - 1
        if(isForward):
           copy_cfg[0][1]["meta"]["pred"].remove(keylen)
        else:
           for key, sub_dict in copy_cfg.items():
               #print(type(sub_dict[1]["meta"]["suc"]))
               if keylen in sub_dict[1]["meta"]["suc"]:
                         sub_dict[1]["meta"]["suc"].remove(keylen)

        copy_cfg.pop(keylen)
        return copy_cfg

    def populate_with_dominance_info(self,prev_analysis):
        #self.print_instrs(prev_analysis)
        #unfortunately our dfa is geared towards running per instruction basis
        #we need to fix this in some future iteration
        node_list = list(prev_analysis.keys())
        def dom_transfer(instr,currentmeta):
            #really bad ik
            clone_meta = currentmeta.copy()
            block_pos = int(instr["position"][0])
            return do_union([clone_meta,[block_pos]])
        dominators = self.dfa_do_work_list(True,prev_analysis,[],node_list,do_intersection,dom_transfer,"dominators",[],[])
        post_dom = self.dfa_do_work_list(False,dominators,node_list,[],do_intersection,dom_transfer,"post_dominators",[],[])
        #self.print_analysis(post_dom,"dominators")
        #self.print_analysis(post_dom,"post_dominators")
        def create_strict(pdom):
            for key, sub_dict in pdom.items():
                sub_dict[1]["meta"]["sdom"] = [dominator for dominator in sub_dict[1]["meta"]["dominators"][-1]["out"] if dominator != key]

        def create_imm(pdom):
            #dominators occur in-order for a path taken
            #all we have to do is see if a given node's sdom is dominated by more than 1 thing
            #if so take the last thing that occured as this nodes idom
            for key, sub_dict in pdom.items():
                if(len(sub_dict[1]["meta"]["sdom"])>=1):
                   sub_dict[1]["meta"]["idom"] = [sub_dict[1]["meta"]["sdom"][-1]]
                else:
                   sub_dict[1]["meta"]["idom"] = [sub_dict[1]["meta"]["sdom"]]
                #print(key," -------->",sub_dict[1]["meta"]["sdom"])

        def find_frontiers(pdom):
            #initialize with empty frontiers
            for key, sub_dict in pdom.items():
                sub_dict[1]["meta"]["df"] = []
            #for each node update frontiers
            for key, sub_dict in pdom.items():
                #predecessors dominators
                pred_dom = do_union([pdom[pred][1]["meta"]["dominators"][-1]["out"] for pred in sub_dict[1]["meta"]["pred"]])
                cn_sdom = sub_dict[1]["meta"]["sdom"]
                #print(key,"fd: ",cn_sdom)
                for dom in pred_dom:
                    if dom not in cn_sdom:
                       #print(pdom[dom])
                       pdom[dom][1]["meta"]["df"].append(key)

        def find_backedges(intrest,visited_list=[],backedges=[]):
            #keep jumping forward using sucessors of node in a dfs fashion
            #if some node points to already visited node its a backedge
            visited_list.append(intrest)
            sucessors = post_dom[intrest][1]["meta"]["suc"]
            #print(sucessors)
            visited_clone =  visited_list.copy()
            for mem in sucessors:
                if mem in visited_list:
                   track = [intrest,mem]
                   if track not in backedges:
                      backedges.append(track)
                else:
                   find_backedges(mem,visited_clone,backedges)

        def create_dom_tree():
            self.tree = []
            for key, sub_dict in post_dom.items():
                node_child = {key:[]}
                for subkey, sub_sub_dict in post_dom.items():
                    #print(sub_sub_dict[1]["meta"]["sdom"])
                    if key in sub_sub_dict[1]["meta"]["idom"]: node_child[key].append(subkey)
                self.tree.append(node_child)

        create_strict(post_dom)
        create_imm(post_dom)
        find_frontiers(post_dom)
        self.backedges = []
        find_backedges(0,[],self.backedges)
        #print("backedges : ",self.backedges)
        create_dom_tree()
        print("--------------------------------")
        for key, sub_dict in post_dom.items():
                 print("df ",key,sub_dict[1]["meta"]["df"])
        print("--------------------------------")
        print("tree ",self.tree)
        self.dom_info = post_dom

    def to_ssa(self,cfg_meta):
        print("meta---------",cfg_meta)
        dom_tree = dict(ChainMap(*self.tree))
        print(dom_tree)
        def build_map(cfg):
            var_assigns_to_map = {}
            for key, sub_dict in cfg.items():
                instrs = sub_dict[0]
                for instr in instrs:
                    #print(instr)
                    if "dest" in instr:
                        dest = instr["dest"]
                        if dest in var_assigns_to_map and key not in var_assigns_to_map[dest]:
                           var_assigns_to_map[dest].append(key)
                        elif dest not in var_assigns_to_map:
                           var_assigns_to_map[dest] = [key]
            return var_assigns_to_map

        def insert_phy(cfg,variable_mapping):
            print("mappp",variable_mapping)
            for key, sub_dict in variable_mapping.items():
                itr = 0
                while itr<len(sub_dict):
                    df = cfg[sub_dict[itr]][1]["meta"]["df"]
                    print(df,key,sub_dict,itr)
                    for i in df:
                       phi = copy.deepcopy(instr_ref["phi"])
                       phi["args"] = []
                       phi["labels"] = []
                       phi["dest"] = key
                       inss = cfg[i][0]
                       phis = [ins for ins in inss if "op" in ins and ins["op"] == "phi"]
                       insert = True
                       for ph in phis:
                           if ph["dest"] == key:
                                insert = False
                                break
                       if insert:
                          sub_dict.append(i)
                          cfg[i][0].insert(1,phi)
                    itr+=1

        def perform_ssa_transform(block,blk_num,curr_var_mapping,newssablock,updated):
            curr_jmp_to = dom_tree[blk_num]
            newinsns = []
            instrs = block[0]
            cblock_names = []
            lbl = instrs[0]["label"]
            succs = block[1]["meta"]["suc"]
            for instr in instrs:
                nargs = []
                if "args" in instr and instr["op"] != "phi":
                   for arg in instr["args"]:
                       if curr_var_mapping[arg] == []: continue
                       nargs.append(curr_var_mapping[arg][-1])
                   if nargs!= []:
                      instr["args"] = nargs

                if "dest" in instr:
                       gen = updated[instr["dest"]]
                       oname = instr["dest"]
                       print(instr["dest"],gen)
                       nname = instr["dest"] + "." + str(gen+1)
                       if nname not in curr_var_mapping[instr["dest"]]:
                          curr_var_mapping[instr["dest"]].append(nname)
                       updated[instr["dest"]] = gen+1
                       cblock_names.append(nname)
                       instr["dest"] = nname

                newinsns.append(instr)

            for suc in succs:
                sinstrs = cfg_meta[suc][0]
                for i in sinstrs:
                    if "op" in i and i["op"] ==  "phi":
                       if i["dest"] not in curr_var_mapping:
                          i["args"].append(curr_var_mapping[i["dest"][:-2]][-1])
                       elif(curr_var_mapping[i["dest"]] == []):
                          i["args"].append("__undefined")
                       else:
                          i["args"].append(curr_var_mapping[i["dest"]][-1])
                       i["labels"].append(lbl)

            newssablock[blk_num] = [newinsns,block[1]]

            for jmp in curr_jmp_to:
                perform_ssa_transform(cfg_meta[jmp],jmp,curr_var_mapping,newssablock,updated)

            for var,ssa_names in curr_var_mapping.items():
                for name in ssa_names:
                    if name in cblock_names:
                       curr_var_mapping[var].remove(name)

        var_map = build_map(cfg_meta)
        insert_phy(cfg_meta,var_map)
        for key,var in var_map.items():
            var_map[key] = []
        for arg in self.func_args:
            var_map[arg] = []
        nblock = {}
        blk = copy.deepcopy(var_map)
        print(blk)
        for keys,sub_dict in blk.items():
            blk[keys] = -1
        print(blk)

        perform_ssa_transform(cfg_meta[0],0,var_map,nblock,blk)

        def reaching_(instr,currentmeta):
            currentmeta1 = currentmeta.copy()
            if "dest" not in instr:
               return currentmeta1
            currentmeta1.append(instr["dest"])
            return currentmeta1

        analysis = self.dfa_do_work_list(True,nblock,[],[],do_union,reaching_,"ssa_reachingdefs",[],[])
        self.print_analysis(analysis,"ssa_reachingdefs")
        print("SML OP")
        self.print_orig(analysis,True,dom_tree)
        print("SSA OP")
        self.print_orig(analysis,False,dom_tree)
        print("OUT END")

if __name__ == "__main__":
    path = sys.argv[1]
    bril_json = open(path, "r").read()
    bril_dict = json.loads(bril_json)
    copy_dict= copy.deepcopy(bril_dict)
    cfg_artifacts = []
    for function,copy_func in zip(bril_dict["functions"],copy_dict["functions"]):
        unmodified_func = function
        instructions = function["instrs"]
        cfg = create_cfg(function)
        cfg_artifacts.append(cfg)
        function.update({'cfg':cfg.cfg})
        optim_obj = optimize_ir(function)
        #instrs = [ elem for elems in optim_obj.lvn_blocks for elem in elems ] #little trick to flatten list
        #copy_func["instrs"] = instrs
