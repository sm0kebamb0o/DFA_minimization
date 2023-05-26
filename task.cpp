#include "api.hpp"

#include <string>
#include <unordered_map>
#include <memory>
#include <set>
#include <unordered_set>
#include <queue>

using Id = unsigned;

namespace MTR{
    class StatesTable{
    public:
        StatesTable(const std::set<std::string> &states){
            Id cur{};
            for (auto &state : states){
                auto it = states_to_ids_.emplace(state, cur).first;
                ids_to_states_.push_back(it);
                ++cur;
            }
            ids_to_states_.shrink_to_fit();
        }

        Id operator[](const std::string &state) const{
            return states_to_ids_.at(state);
        }

        std::string operator[](Id id) const{
            return ids_to_states_.at(id)->first;
        }

        auto size() const{ return ids_to_states_.size(); }

        std::unordered_set<Id> get_states_ids() const{
            std::unordered_set<Id> states_ids;
            for (auto &state_to_id : states_to_ids_){
                states_ids.insert(state_to_id.second);
            }
            return states_ids;
        }

    private:
        std::unordered_map<std::string, Id> states_to_ids_;
        std::vector<std::unordered_map<std::string, Id>::iterator> ids_to_states_;
    };

    template <typename T>
    class LadderArray{
    public:

        LadderArray(Id size) : size_(size){
            array_ = std::make_unique<T[]>((size * (size - 1)) >> 1);
        }

        T &operator()(Id i, Id j) const{
            return array_[((i * (i - 1)) >> 1) + j];
        }

        auto size() const{ return size_; }
    private:
        std::size_t size_;
        std::unique_ptr<T[]> array_;
    };

    namespace{
        std::string DeadState("Dead State");

        void DeleteUnreachableStates(DFA &dfa,
                                     StatesTable &states,
                                     Alphabet &terminals){
            std::unordered_set<Id> unreachable_states_ids(states.get_states_ids());

            std::queue<Id> states_traversal;
            states_traversal.push(states[dfa.get_initial_state()]);

            while (!states_traversal.empty()){
                Id state_id = states_traversal.front();
                states_traversal.pop();

                if (unreachable_states_ids.find(state_id) == unreachable_states_ids.end()) continue;

                unreachable_states_ids.erase(state_id);

                for (auto terminal : terminals){
                    if (dfa.has_trans(states[state_id], terminal)){
                        states_traversal.push(states[dfa.get_trans(states[state_id], terminal)]);
                    }
                }
            }

            for (Id unreachable_state_id : unreachable_states_ids){
                dfa.delete_state(states[unreachable_state_id]);
            }
        }

        void AddDeadState(DFA &dfa,
                          StatesTable &states,
                          Alphabet &terminals){
            dfa.create_state(DeadState);
            for (auto terminal : terminals){
                dfa.set_trans(DeadState, terminal, DeadState);
            }

            const auto states_ids = states.get_states_ids();

            for (Id state_id : states_ids){
                for (auto terminal : terminals){
                    if (!dfa.has_trans(states[state_id], terminal)){
                        dfa.set_trans(states[state_id], terminal, DeadState);
                    }
                }
            }
        }

        void InitializeDistinctStates(LadderArray<bool> &distinct_states,
                                      DFA &dfa,
                                      StatesTable &states){
            std::unordered_set<Id> final_states_ids;

            for (auto &final_state : dfa.get_final_states()){
                final_states_ids.insert(states[final_state]);
            }

            for (Id i = 1; i < states.size(); ++i){
                for (Id j = 0; j < i; ++j){
                    if ((final_states_ids.find(i) != final_states_ids.end()) ^
                        (final_states_ids.find(j) != final_states_ids.end())){
                        distinct_states(i, j) = true;
                    }
                }
            }
        }

        void DefineDistinctStates(LadderArray<bool> &distinct_states,
                                  DFA &dfa,
                                  StatesTable &states,
                                  Alphabet &terminals){
            bool changed = true;

            while (changed){
                changed = false;
                for (Id i = 1; i < states.size(); ++i){
                    for (Id j = 0; j < i; ++j){
                        if (distinct_states(i, j)) continue;

                        for (auto terminal : terminals){
                            if (dfa.has_trans(states[i], terminal) &&
                                dfa.has_trans(states[j], terminal)){
                                auto state_to_i = states[dfa.get_trans(states[i], terminal)];
                                auto state_to_j = states[dfa.get_trans(states[j], terminal)];

                                if (state_to_j > state_to_i) std::swap(state_to_i, state_to_j);

                                if (!(state_to_i == state_to_j) && distinct_states(state_to_i, state_to_j)){
                                    distinct_states(i, j) = true;
                                    changed = true;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
        }

        Id CreateNewStates(LadderArray<bool> &distinct_states,
                           DFA &dfa_old,
                           DFA &dfa_new,
                           std::vector<Id> &old_states_to_new_states,
                           std::vector<std::unordered_set<Id>> &new_states_to_old_states){
            Id new_id{};
            std::string first_state_name = std::to_string(new_id);

            dfa_new.create_state(first_state_name);
            old_states_to_new_states[0] = new_id;
            new_states_to_old_states[new_id].insert(0);
            ++new_id;

            bool distinct_state;
            Id equal_state_id;
            for (Id i = 1; i < distinct_states.size(); ++i){
                distinct_state = true;
                for (Id j = 0; j < i; ++j){
                    if (!distinct_states(i, j)){
                        distinct_state = false;
                        equal_state_id = j;
                        break;
                    }
                }
                if (distinct_state){
                    dfa_new.create_state(std::to_string(new_id));
                    old_states_to_new_states[i] = new_id;
                    new_states_to_old_states[new_id].insert(i);
                    ++new_id;
                } else{
                    Id new_state_id = old_states_to_new_states[equal_state_id];
                    old_states_to_new_states[i] = new_state_id;
                    new_states_to_old_states[new_state_id].insert(i);
                }
            }
            return new_id;
        }

        void CreateNewTranses(LadderArray<bool> &distinct_states,
                              StatesTable &states,
                              Alphabet &terminals,
                              DFA &dfa_old,
                              DFA &dfa_new,
                              std::vector<Id> &old_states_to_new_states,
                              std::vector<std::unordered_set<Id>> &new_states_to_old_states){

            for (Id new_state_id = 0; new_state_id < new_states_to_old_states.size(); ++new_state_id){

                std::string new_state = std::to_string(new_state_id);
                bool is_final = false;

                for (Id old_state_id : new_states_to_old_states[new_state_id]){
                    if (!is_final && dfa_old.is_final(states[old_state_id])){
                        dfa_new.make_final(new_state);
                        is_final = true;
                    }

                    for (auto terminal : terminals){
                        if (!dfa_old.has_trans(states[old_state_id], terminal)) continue;

                        Id old_state_to_id = states[dfa_old.get_trans(states[old_state_id], terminal)];
                        Id new_state_to_id = old_states_to_new_states[old_state_to_id];

                        dfa_new.set_trans(new_state, terminal, std::to_string(new_state_to_id));
                    }
                }
            }
        }
    };

    void TransformDFA(DFA &dfa){
        StatesTable states(dfa.get_states());
        Alphabet terminals = dfa.get_alphabet();

        DeleteUnreachableStates(dfa, states, terminals);

        AddDeadState(dfa, states, terminals);
    }

    void FindDistinctStates(LadderArray<bool> &distinct_states,
                            DFA &dfa,
                            StatesTable &states,
                            Alphabet &terminals){
        InitializeDistinctStates(distinct_states, dfa, states);

        DefineDistinctStates(distinct_states, dfa, states, terminals);
    }

    void CreateNewDFA(LadderArray<bool> &distinct_states,
                      StatesTable &states,
                      Alphabet &terminals,
                      DFA &dfa_old,
                      DFA &dfa_new){
        std::vector<Id> old_states_to_new_states(states.size());
        std::vector<std::unordered_set<Id>> new_states_to_old_states(states.size());

        Id last_new_id = CreateNewStates(distinct_states,
                                         dfa_old, dfa_new, 
                                         old_states_to_new_states, 
                                         new_states_to_old_states);
        new_states_to_old_states.resize(last_new_id);
        new_states_to_old_states.shrink_to_fit();

        Id old_initial_state_id = states[dfa_old.get_initial_state()];
        dfa_new.set_initial(std::to_string(old_states_to_new_states[old_initial_state_id]));

        CreateNewTranses(distinct_states, states, terminals, dfa_old, dfa_new, 
                         old_states_to_new_states, new_states_to_old_states);

        Id old_dead_state_id = states[DeadState];
        dfa_new.delete_state(std::to_string(old_states_to_new_states[old_dead_state_id]));
    }
};

DFA dfa_minim(DFA &dfa) {

    MTR::TransformDFA(dfa);

    Alphabet terminals = dfa.get_alphabet();
    MTR::StatesTable states(dfa.get_states());

    MTR::LadderArray<bool> distinct_states(states.size());
    MTR::FindDistinctStates(distinct_states, dfa, states, terminals);

    DFA res_dfa(terminals);
    MTR::CreateNewDFA(distinct_states, states, terminals, dfa, res_dfa);

    if (!res_dfa.size()){
        res_dfa.create_state("0");
        res_dfa.set_initial("0");
    }

    return res_dfa;
}
