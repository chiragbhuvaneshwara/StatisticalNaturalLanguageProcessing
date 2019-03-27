"""
Created on Sat Aug 11 11:03:57 2018

@authors: Chirag Bhuvaneshwara, Ayan Majumdar, Hui-Syuan Yeh 

"""

import sys, os, string
from functools import wraps

def hamming(s,t):
    # Compute the Hamming distance between the strings s and t.
    return sum(1 for x,y in zip(s,t) if x != y)    

def halign(s,t):
    # Align the two strings s and t by using Hamming.
    slen = len(s)
    tlen = len(t)    
    #Start with worst possible score
    minscore = len(s) + len(t) + 1
    #Now align the two strings such that cost or score is minimized.
    for upad in range(0, len(t)+1):
        upper = '_' * upad + s + (len(t) - upad) * '_'
        lower = len(s) * '_' + t
        score = hamming(upper, lower)
        if score < minscore:
            bu = upper
            bl = lower
            minscore = score

    for lpad in range(0, len(s)+1):
        upper = len(t) * '_' + s
        lower = (len(s) - lpad) * '_' + t + '_' * lpad
        score = hamming(upper, lower)
        if score < minscore:
            bu = upper
            bl = lower
            minscore = score

    zipped = zip(bu,bl)
    newin  = ''.join(i for i,o in zipped if i != '_' or o != '_')
    newout = ''.join(o for i,o in zipped if i != '_' or o != '_')
    return newin, newout

def levenshtein(s, t, inscost = 1.0, delcost = 1.0, substcost = 1.0):
    # Implements Levenshtein in a recursive fashion, and also returns the corresponding alignments.
    @memolrec
    def lrec(spast, tpast, srem, trem, cost):
        if len(srem) == 0:
            return spast + len(trem) * '_', tpast + trem, '', '', cost + len(trem)
        if len(trem) == 0:
            return spast + srem, tpast + len(srem) * '_', '', '', cost + len(srem)

        addcost = 0
        if srem[0] != trem[0]:
            addcost = substcost
            
        return min((lrec(spast + srem[0], tpast + trem[0], srem[1:], trem[1:], cost + addcost),
                   lrec(spast + '_', tpast + trem[0], srem, trem[1:], cost + inscost),
                   lrec(spast + srem[0], tpast + '_', srem[1:], trem, cost + delcost)),
                   key = lambda x: x[4])

    answer = lrec('', '', s, t, 0)
    return answer[0],answer[1],answer[4]

def memolrec(func):
    """Memoizer for Levenshtein."""
    cache = {}
    @wraps(func)
    def wrap(sp, tp, sr, tr, cost):
        if (sr,tr) not in cache:
            res = func(sp, tp, sr, tr, cost)
            cache[(sr,tr)] = (res[0][len(sp):], res[1][len(tp):], res[4] - cost)
        return sp + cache[(sr,tr)][0], tp + cache[(sr,tr)][1], '', '', cost + cache[(sr,tr)][2]
    return wrap
    
def alignprs(lemma, form):
    """Break lemma/form into three parts:
    IN:  1 | 2 | 3
    OUT: 4 | 5 | 6
    1/4 are assumed to be prefixes, 2/5 the stem, and 3/6 a suffix.
    1/4 and 3/6 may be empty.
    """
    
    al = levenshtein(lemma, form, substcost = 1.1) # Force preference of 0:x or x:0 by 1.1 cost
    alemma, aform = al[0], al[1]
    # leading spaces
    lspace = max(len(alemma) - len(alemma.lstrip('_')), len(aform) - len(aform.lstrip('_')))
    # trailing spaces
    tspace = max(len(alemma[::-1]) - len(alemma[::-1].lstrip('_')), len(aform[::-1]) - len(aform[::-1].lstrip('_')))
    return alemma[0:lspace], alemma[lspace:len(alemma)-tspace], alemma[len(alemma)-tspace:], aform[0:lspace], aform[lspace:len(alemma)-tspace], aform[len(alemma)-tspace:]

def get_prefix_suffix_changes(lemma, inflection_form):
    """Extract a number of suffix-change and prefix-change rules
    based on a given example lemma+inflected form."""
    lem_pref,lem_root,lem_suf,infl_pref,infl_root,infl_suf = alignprs(lemma, inflection_form) # Get six parts, three for in three for out
    # Suffix rules  
    lem_str = lem_root + lem_suf + '$'
    infl_str = infl_root + infl_suf + '$' 
    suf_changes = []
    # Store all the possible suffix changes that are possible to generate.
    for i in range(min(len(lem_str), len(infl_str))):
        suf_changes.append((lem_str[i:], infl_str[i:]))
    suf_changes = [(x[0].replace('_',''), x[1].replace('_','')) for x in suf_changes]
    suf_changes = set(suf_changes)

    # Prefix rules
    pref_changes = []
    lem_str = "@" + lem_pref
    infl_str = "@" + infl_pref
    for i in range(0,len(infl_root)):
        pref_changes.append((lem_str + infl_root[:i], infl_str + infl_root[:i]))
    pref_changes = [(x[0].replace('_',''), x[1].replace('_','')) for x in pref_changes]
    pref_changes = set(pref_changes)
    
    return pref_changes, suf_changes

def generate_inflection(lemma, infl_rule, prefix_rules_dict, suffix_rules_dict):
    """Applies the longest-matching suffix-changing rule given an input
    form and the MSD. Length ties in suffix rules are broken by frequency.
    For prefix-changing rules, only the most frequent rule is chosen."""
    
    base = "@" + lemma + "$"
    # If this rule has not been seen, just return original form
    if infl_rule not in prefix_rules_dict and infl_rule not in suffix_rules_dict:
        return lemma 

    # Check the best possible suffix rule to apply
    # So, find longest suffix match, if tied, break tie by frequency.
    if infl_rule in suffix_rules_dict:
        valid_rules = [(x[0],x[1],y) for x,y in suffix_rules_dict[infl_rule].items() if x[0] in base]
        if valid_rules:
            best_rule = max(valid_rules, key = lambda x: (len(x[0]), x[2]))           
            base = base.replace(best_rule[0], best_rule[1])
        
    # Check the best possible prefix rule to apply
    # That is the most frequent prefix rule for the given inflection rule
    if infl_rule in prefix_rules_dict:
        valid_rules = [(x[0],x[1],y) for x,y in prefix_rules_dict[infl_rule].items() if x[0] in base]
        if valid_rules:
            best_rule = max(valid_rules, key = lambda x: (x[2]))
            base = base.replace(best_rule[0], best_rule[1])
                
    base = base.replace('$', '')
    base = base.replace('@', '')
    return base
    
###############################################################################

def main(argv):
    
    # Code to take care of all the flags that the command line can take
    s = argv[1:]
    show_accuracy, show_output = False, False 
    
    # if '-g' in s and ('-tr' or '-te' or '-l' or '-a') not in s and (len(s)<2):
    # If -g is used, simply print group info and quit
    if '-g' in s:
        g0 = "Group L02: Faroese"
        g1 = "Ayan Majumdar, 2571656"
        g2 = "Chirag Bhuvaneshwara, 2571703"
        g3 = "Hui-Syuan Yeh, 2571618"
        print("\n"+g0+"\n"+g1+"\n"+g2+"\n"+g3+"\n")
        return 0
    # Both -tr and -te are mandatory
    elif ('-tr' and '-te' in s) and (len(s)<7):
        # Either -l or -a is mandatory
        if ('-l' or '-a' in s):
        
            trindex = s.index('-tr')
            train_path = s[trindex + 1]
            teindex = s.index('-te')
            test_path = s[teindex + 1]

            if '-l' in s:
                show_output = True

            if '-a' in s:
                show_accuracy = True
        else:
            return -1
    else:
        return -1
    
    prefix_rules_dict, suffix_rules_dict = {}, {}
    instances = 0
    train_file_lines = []

    with open(train_path, 'r', encoding='utf-8') as f:
        for line in f:
            train_file_lines.append(line.strip())

    # Seeing whether the language is more prefix oriented or suffix oriented
   
    prefix_cnt, suffix_cnt = 0,0
    for l in train_file_lines:
        lemma, inflection_form, _ = l.split()
        pref_suff_aligned_tokens = halign(lemma, inflection_form)
        if ' ' not in pref_suff_aligned_tokens[0] and ' ' not in pref_suff_aligned_tokens[1]:
            prefix_cnt += (len(pref_suff_aligned_tokens[0]) - len(pref_suff_aligned_tokens[0].lstrip('_'))) + (len(pref_suff_aligned_tokens[1]) - len(pref_suff_aligned_tokens[1].lstrip('_')))
            suffix_cnt += (len(pref_suff_aligned_tokens[0]) - len(pref_suff_aligned_tokens[0].rstrip('_'))) + (len(pref_suff_aligned_tokens[1]) - len(pref_suff_aligned_tokens[1].rstrip('_')))

    if prefix_cnt > suffix_cnt:
        LANG_PREFIXED = True
    else:
        LANG_PREFIXED = False

    # Obtaining the transformation rules 
    # If the language is prefix oriented, the strings are reversed as in the project description
    for l in train_file_lines:
        instances += 1
        lemma, inflection_form, infl_rule = l.split()

        # Use the heuristic described. If language is suffix based, reverse the strings.
        if LANG_PREFIXED:
            lemma = lemma[::-1]
            inflection_form = inflection_form[::-1]
        
        #Extracting prefix rules and suffix rules
        pref_rules, suff_rules = get_prefix_suffix_changes(lemma, inflection_form)
        
        
        if infl_rule not in prefix_rules_dict and len(pref_rules) > 0:
            prefix_rules_dict[infl_rule] = {}
        if infl_rule not in suffix_rules_dict and len(suff_rules) > 0:
            suffix_rules_dict[infl_rule] = {}

        for r in pref_rules:
            if (r[0],r[1]) in prefix_rules_dict[infl_rule]:
                prefix_rules_dict[infl_rule][(r[0],r[1])] = prefix_rules_dict[infl_rule][(r[0],r[1])] + 1
            else:
                prefix_rules_dict[infl_rule][(r[0],r[1])] = 1

        for r in suff_rules:
            if (r[0],r[1]) in suffix_rules_dict[infl_rule]:
                suffix_rules_dict[infl_rule][(r[0],r[1])] = suffix_rules_dict[infl_rule][(r[0],r[1])] + 1
            else:
                suffix_rules_dict[infl_rule][(r[0],r[1])] = 1

    # Testing using the test file
    test_file_lines = []
    checked = False
    test_num_cols = 0
    with open(test_path, 'r', encoding='utf-8') as f:
        for line in f:
            test_file_lines.append(line.strip())
            if not checked:
                checked = True
                test_num_cols = len(line.strip().split())

    if test_num_cols != 3 and test_num_cols != 2:
        print("INVALID TEST FILE PROVIDED")
        return -1

    #devlines = [line.strip() for line in codecs.open(test_path , "r", encoding="utf-8")]

    correct_preds = 0
    test_instances = 0
        
    # Test file can be 2 or 3 column format
    for l in test_file_lines:
        if test_num_cols == 3:
            lemma, correct, rule, = l.split()
        elif test_num_cols == 2:
            lemma, rule = l.split()
        lemmaorig = lemma
        #Reversing the strings if prefix oriented
        if LANG_PREFIXED:
            lemma = lemma[::-1]
        
        #Applying the longest matching rule
        outform = generate_inflection(lemma, rule, prefix_rules_dict, suffix_rules_dict)
        
        #Reversing the reversed string before output
        if prefix_cnt > suffix_cnt:
            outform = outform[::-1]
        if test_num_cols == 3:
            if outform == correct:
                correct_preds += 1
        test_instances += 1
        
        if show_output==True:  
            print(lemmaorig + "\t" + rule + "\t" + outform + "\n")
            
    if show_accuracy==True and test_num_cols == 3:
        print("\nTrained on:", train_path)
        print("- Training instances:", instances)
        print("Tested on:", test_path)
        print("- Testing instances:", test_instances)
        print("- Correct instances:", correct_preds)
        print("- Accuracy : %2.2f" %((correct_preds*100)/float(test_instances)) + "%" )
        print()
    elif show_accuracy == True and test_num_cols == 2:
        print("\nTrained on:", train_path)
        print("- Training instances:", instances)
        print("Tested on:", test_path)
        print("- Testing instances:", test_instances)
        print("Cannot show correct instances as they are not present in test file provided.\n")
    return 0

if __name__ == "__main__":
    main(sys.argv)