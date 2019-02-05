import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact])
        ####################################################
        # Student code goes here

        if fact.asserted and len(fact.supported_by) == 0:
            queue = [fact]

            while len(queue) > 0:
                print(queue)
                temp = []
                for f in self.facts: # index through facts
                    for i in range(len(f.supported_by)): # index through supported_by within each fact
                        if queue[0] in f.supported_by[i]: # check first element in the pair
                            f.supported_by.pop(i) # remove corresponding fact/rule pair
                            temp.append(f)

                for r in self.rules: # index through rules
                    for i in range(len(r.supported_by)): # index through supported_by within each rule
                        if queue[0] in r.supported_by[i]: # check second element in the pair
                            r.supported_by.pop(i) # remove corresponding fact/rule pair
                            temp.append(r)

                for i in range(len(temp)):
                    # check to see if they don't meet requirements to be removed
                    if len(temp[i].supported_by) != 0:
                        temp[i] == False
                    elif type(temp[i]) == Rule and temp[i].asserted == True:
                        temp[i] == False
                    # if they pass all checks, add it to the end of the list
                    if temp[i]:
                        queue.append(temp[i])

                # delete the current fact/rule from the kb
                if type(queue[0]) == Fact:
                    print(type(queue[0]))

                    for i in range(len(self.facts)):
                        if queue[0] == self.facts[i]:
                            self.facts.pop(i)

                if type(queue[0]) == Rule:
                    for i in range(len(self.rules)):
                        if queue[0] == self.rules[i]:
                            self.rules.pop(i)

                # remove from the queue
                queue = queue[1:]

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here

        if match(fact.statement, rule.lhs[0], None):

            bind_new = match(fact.statement, rule.lhs[0], None) # hold bindings
            # print('BINDINGS:' + str(bind_new))

            #set rhs, lhs
            rhs_new = instantiate(rule.rhs, bind_new)
            lhs_new = rule.lhs[1:]

            if len(lhs_new) == 0: # this is when we need to make a fact, not a rule
                fact_new = Fact(rhs_new,[[fact, rule]])
                '''
                repeat = False
                for i in range(len(kb.facts)):
                    if fact_new == kb.facts[i]:
                        repeat = True
                if not repeat:
                    kb.facts.append(fact_new)
                '''

                kb.kb_assert(fact_new)
                # print('FACT ADDED:' + str(fact_new))

                fact.supports_facts.append(fact_new)
                rule.supports_rules.append(fact_new)

            else: # make a new rule
                for i in range(len(lhs_new)):
                    lhs_new[i] = instantiate(lhs_new[i], bind_new)



                # create new rule, add it to rules list in kb if not a repeat
                rule_new = Rule([lhs_new, rhs_new], [[fact, rule]])
                '''
                repeat = False
                for i in range(len(kb.rules)):
                    if rule_new == kb.rules[i]:
                        repeat = True
                if not repeat:
                    kb.rules.append(rule_new)
                '''

                kb.kb_assert(rule_new)
                # print('RULE ADDED: ' + str(rule_new))

                # update supports_rules in fact, rule
                fact.supports_rules.append(rule_new)
                rule.supports_rules.append(rule_new)
