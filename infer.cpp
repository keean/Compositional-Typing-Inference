// Copyright 2012, 2013, 2014 Keean Schupke
// compile with g++ -std=gnu++11 

#include <string>
#include <vector>
#include <iostream>
#include <iomanip>
#include <memory>
#include <fstream>
#include <stdexcept>
#include <vector>
#include <map>
#include <set>
#include <sstream>
#include <algorithm>

#include "profile.hpp"
#include "parser_combinators.hpp"

using namespace std;

//----------------------------------------------------------------------------
// Type Expression Graph

class ast {};

class type_expression : public ast {
    type_expression *canonical;
    int rank;

protected:
    type_expression() : canonical(this), rank(0) {}

public:
    virtual void accept(class type_visitor *v) = 0;
    
    void replace_with(type_expression *e) {
        if (rank == e->rank) {
            ++(e->rank);
        }
        canonical = e;
    };

    // find the canonical type
    friend type_expression* find(type_expression* e) {
        while (e->canonical->canonical != e->canonical) {
            e = (e->canonical = e->canonical->canonical);
        }
        return e->canonical;
    }

    // let the algorithm pick the most efficient substitution
    friend type_expression* link(type_expression* x, type_expression* y) {
        if (x->rank > y->rank) {
            swap(x, y);
        } else if (x->rank == y->rank) {
            ++(y->rank);
        }
        x->canonical = y;
        return y;
    }
};

typedef vector<type_expression*> row_type;

class type_literal : public type_expression {
    friend class ast_factory;
    explicit type_literal(string const &name) : name(name) {}
    type_literal(string const &name, row_type &&params) : name(name), params(params) {}

public:
    string const name;
    row_type const params;
    virtual void accept(class type_visitor *v) override;
};

class type_variable : public type_expression {
    friend class ast_factory;
    static int next;

protected:
    type_variable() : id(++next) {}
    type_variable(int const id) : id(id) {}

public:
    int const id;
    virtual void accept(class type_visitor *v) override;
};

int type_variable::next(0);

class type_application : public type_expression {
    friend class ast_factory;
    type_application(type_expression *dom, type_expression *cod) : dom(dom), cod(cod) {}

public:
    //type_expression *const dom, *const cod;
    type_expression *dom, *cod;
    virtual void accept(class type_visitor *v) override;
};

class type_product : public type_expression {
    friend class ast_factory;
    type_product(type_expression *left, type_expression *right) : left(left), right(right) {}

public:
    type_expression *const left, *const right;
    virtual void accept(class type_visitor *v) override;
};

struct type_visitor {
    virtual void visit(type_literal *t) = 0;
    virtual void visit(type_variable *t) = 0;
    virtual void visit(type_application *t) = 0;
    virtual void visit(type_product *t) = 0;
};

void type_literal::accept(class type_visitor *v) {v->visit(this);}
void type_variable::accept(class type_visitor *v) {v->visit(this);}
void type_application::accept(class type_visitor *v) {v->visit(this);}
void type_product::accept(class type_visitor *v) {v->visit(this);}

//----------------------------------------------------------------------------
// Term Expression AST

typedef multimap<string, type_expression*> mono_env_type;

typedef pair<mono_env_type, type_expression*> typing_type;

/*
struct typing_type {
    mono_env_type mono_env;
    type_expression* type;
};

// [{x : a -> b, x -> a} |- y : b]

typedef multimap<string, typing_type> poly_env_type;

// [{x : a -> b, x -> a} |- y : b] {x : a ->b, x : a} |- y = x x; y : b

struct modular_type {
    // exports
    poly_env_type poly_env;

    // requirements
    mono_env_type mono_env;

    // result type
    type_expression* type;
};
*/

struct term_expression : public ast {
    //modular_type mod_type;
    typing_type typing;
    virtual void accept(class term_visitor *v) = 0;
};

class term_literal : public term_expression {
    friend class ast_factory;
    explicit term_literal(int value) : value(value) {}

public:
    int const value;
    virtual void accept(class term_visitor *v) override;
};

class term_variable : public term_expression {
    friend class ast_factory;
    explicit term_variable(string const& name) : name(name) {}

public:
    string const name;
    virtual void accept(class term_visitor *v) override;
};

class term_application : public term_expression {
    friend class ast_factory;
    term_application(term_expression *fun, term_expression *arg)
    : fun(fun), arg(arg) {}

public:
    term_expression *const fun, *const arg;
    virtual void accept(class term_visitor *v) override;
};

class term_abstraction : public term_expression {
    friend class ast_factory;
    term_abstraction(string const& name, term_expression *body)
    : name(name), body(body) {}

public:
    string const name;
    term_expression* const body;
    virtual void accept(class term_visitor *v) override;
};

class term_let : public term_expression {
    friend class ast_factory;
    term_let(string const& name, term_expression *rhs, term_expression *body)
    : name(name), rhs(move(rhs)), body(body) {}

public:
    string const name;
    term_expression *const rhs, *const body;
    virtual void accept(class term_visitor *v) override;
};

class term_product : public term_expression {
    friend class ast_factory;
    term_product(term_expression *lhs, term_expression *rhs) : rhs(rhs), lhs(lhs) {}

public:
    term_expression *const lhs, *const rhs;
    virtual void accept(class term_visitor *v) override;
};

struct term_visitor {
    virtual void visit(term_literal *t) = 0;
    virtual void visit(term_variable *t) = 0;
    virtual void visit(term_application *t) = 0;
    virtual void visit(term_abstraction *t) = 0;
    virtual void visit(term_let *t) = 0;
    virtual void visit(term_product *t) = 0;
};

void term_literal::accept(class term_visitor *v) {v->visit(this);}
void term_variable::accept(class term_visitor *v) {v->visit(this);}
void term_application::accept(class term_visitor *v) {v->visit(this);}
void term_abstraction::accept(class term_visitor *v) {v->visit(this);}
void term_let::accept(class term_visitor *v) {v->visit(this);}
void term_product::accept(class term_visitor *v) {v->visit(this);}

//----------------------------------------------------------------------------
// RAII AST Factory

class ast_factory {
    vector<unique_ptr<ast>> region;

public:

    // Types
    
    type_literal* new_type_literal(string const &name) {
        unique_ptr<type_literal> e(new type_literal(name));
        type_literal *f = e.get();
        region.push_back(unique_ptr<ast>(move(e)));
        return f;
    }

    type_variable* new_type_variable() {
        unique_ptr<type_variable> e(new type_variable());
        type_variable *f = e.get();
        region.push_back(unique_ptr<ast>(move(e)));
        return f;
    }

    type_application* new_type_application(type_expression *dom, type_expression *cod) {
        unique_ptr<type_application> e(new type_application(dom, cod));
        type_application *f = e.get();
        region.push_back(unique_ptr<ast>(move(e)));
        return f;
    }

    type_product* new_type_product(type_expression *l, type_expression *r) {
        unique_ptr<type_product> e(new type_product(l, r));
        type_product *f = e.get();
        region.push_back(unique_ptr<ast>(move(e)));
        return f;
    }

    // Terms

    term_literal* new_term_literal(int value) {
        unique_ptr<term_literal> e(new term_literal(value));
        term_literal *f = e.get();
        region.push_back(unique_ptr<ast>(move(e)));
        return f;
    }

    term_variable* new_term_variable(string const &name) {
        unique_ptr<term_variable> e(new term_variable(name));
        term_variable *f = e.get();
        region.push_back(unique_ptr<ast>(move(e)));
        return f;
    }

    term_application* new_term_application(term_expression *fun, term_expression *arg) {
        unique_ptr<term_application> e(new term_application(fun, arg));
        term_application *f = e.get();
        region.push_back(unique_ptr<ast>(move(e)));
        return f;
    }

    term_abstraction* new_term_abstraction(string const& name, term_expression *body) {
        unique_ptr<term_abstraction> e(new term_abstraction(name, body));
        term_abstraction *f = e.get();
        region.push_back(unique_ptr<ast>(move(e)));
        return f;
    }

    term_let* new_term_let(string const& name, term_expression *rhs, term_expression *body) {
        unique_ptr<term_let> e(new term_let(name, rhs, body));
        term_let *f = e.get();
        region.push_back(unique_ptr<ast>(move(e)));
        return f;
    }

    term_product* new_term_product(term_expression *lhs, term_expression *rhs) {
        unique_ptr<term_product> e(new term_product(lhs, rhs));
        term_product *f = e.get();
        region.push_back(unique_ptr<ast>(move(e)));
        return f;
    }
};

//----------------------------------------------------------------------------
// Show Type Graph

class type_show : public type_visitor {
    typedef map<int, int> var_map_type;

    set<type_expression*> visited;
    var_map_type tvar_map;

    bool debug;
    int vid;
    ostream &out;

    int type_id(var_map_type &vs, int &v, type_variable const *const t) {
        auto const i = vs.find(t->id);
        if (i == vs.end()) {
            vs[t->id] = v;
            return v++;
        } else {
            return i->second;
        }
    }

public:
    virtual void visit(type_literal *t) override {
        out << t->name;
    }

    virtual void visit(type_variable *t) override {
        static const string vs {"abcdefghijklmnopqrstuvwxyz"};
        int x {type_id(tvar_map, vid, t)};
        string s {};
        do {
            s.push_back(vs[x % 26]);
            x = x / 26;
        } while (x > 0);
        reverse(s.begin(), s.end());
        out << s;
    }

    virtual void visit(type_application *t) override {
        if (visited.count(t) == 0) {
            visited.insert(t);
            out << "(";
            find(t->dom)->accept(this);
        out << " -> ";
            find(t->cod)->accept(this);
            out << ")";
            visited.erase(t);
        } else {
            out << "...";
        }
    }

    virtual void visit(type_product *t) override {
        if (visited.count(t) == 0) {
            visited.insert(t);
            out << "(";
            find(t->left)->accept(this);
            out << " * ";
            find(t->right)->accept(this);
            out << ")";
            visited.erase(t);
        } else {
            out << "...";
        }
    }

    explicit type_show(ostream &out, bool debug = false) : debug(debug), vid(0), out(out) {}

    void operator() (type_expression *t) {
        if (t != nullptr) {
            visited.clear();
            find(t)->accept(this);
        }
    }

    void reset() {
        visited.clear();
        tvar_map.clear();
        vid = 0;
    }
};
    
//----------------------------------------------------------------------------
// Show Term Tree

class term_show : public term_visitor {
    type_show show_type;
    ostream &out;

    void term_show_type(type_expression *t) {
        if (t != nullptr) {
            show_type(t);
        }
    }

    void show_mono_env(mono_env_type &m) {
        if (!(m.empty())) {
            mono_env_type::iterator const f(m.begin());
            mono_env_type::iterator const l(m.end());
            out << "{";
            for (mono_env_type::iterator i(f); i != l; ++i) {
                out << i->first << " : ";
                show_type(i->second);
                mono_env_type::iterator j(i);
                if (++j != l) {
                    out << ", ";
                }
            }
            out << "} "; 
        }
    }

    void show_typing(typing_type &t) {
        show_mono_env(t.first);
        out << "|- ";
        term_show_type(t.second);
    }

/*
    void show_poly_env(poly_env_type &p) {
        if (!(p.empty())) {
            poly_env_type::iterator const f(m.begin());
            poly_env_type::iterator const l(m.end());
            out << "<";
            for (poly_env_type::iterator i(f); i != l; ++i) {
                out << i->first << " : ";
                show_typing(i->second);
                poly_env_type::iterator j(i);
                if (++j != l) {
                    out << ", ";
                }
            }
            out << "> ";
        }
    }

    void show_mod_type(mod_type &s) {
        show_poly_env(s.poly_env);
        out << " ";
        show_mono_env(s.mono_env);
        out << " |- ";
        term_show_type(s.type);
    }
*/

public:
    virtual void visit(term_literal *t) override {
        out << t->value;
    }

    virtual void visit(term_variable *t) override {
        out << t->name;
    }

    virtual void visit(term_application *t) override {
        out << "(";
        t->fun->accept(this);
        out << " ";
        t->arg->accept(this);
        out << ")";
    }

    virtual void visit(term_abstraction *t) override {
        out << "(\\" << t->name << " . ";
        t->body->accept(this);
        out << ")";
    }

    virtual void visit(term_let *t) override {
        out << "(let " << t->name << " = ";
        t->rhs->accept(this);
        out << " in ";
        t->body->accept(this);
        out << ")";
    }

    virtual void visit(term_product *t) override {
        out << "(";
        t->lhs->accept(this);
        out << ", ";
        t->rhs->accept(this);
        out << ")";
    }

    explicit term_show(ostream &out, bool debug = false) : show_type(out, debug), out(out) {}

    void operator() (term_expression *t) {
        if (t != nullptr) {
            t->accept(this);
            out << " : ";
            show_type.reset();
            //show_mod_type(t->mod_type);
            show_typing(t->typing);
        }
    }
};

ostream& operator<< (ostream &out, term_expression* t) {
    term_show show_term(out);
    show_term(t);
    return out;
}
  
//----------------------------------------------------------------------------
// Term Parser 

struct return_app {
    ast_factory& ast;
    return_app(ast_factory &ast) : ast(ast) {}
    void operator() (term_expression **res, term_expression* term) const {
        if (*res == nullptr) {
            *res = term;
        } else {
            *res = ast.new_term_application(*res, term);
        }
    }
};

struct return_abs {
    ast_factory& ast;
    return_abs(ast_factory &ast) : ast(ast) {}
    void operator() (term_expression **res, string &name, term_expression *expr) const {
        *res = ast.new_term_abstraction(name, expr);
    }
};

struct return_let {
    ast_factory& ast;
    return_let(ast_factory &ast) : ast(ast) {}
    void operator() (term_expression **res,
        string const& name, term_expression *rhs, term_expression *body
    ) const {
        *res = ast.new_term_let(name, rhs, body);
    }
};

struct return_var {
    ast_factory& ast;
    return_var(ast_factory &ast) : ast(ast) {}
    void operator() (term_expression **res, string &name) const {
        *res = ast.new_term_variable(name);
    }
};

struct return_num {
    ast_factory& ast;
    return_num(ast_factory &ast) : ast(ast) {}
    void operator() (term_expression **res, string &num) const {
        *res = ast.new_term_literal(stoi(num));
    }
};

auto const num_tok = name("number", tokenise(some(accept(is_digit))));
auto const name_tok = except("let", except("in"
    , name("name", tokenise(some(accept(is_alpha)) && many(accept(is_alnum))))));
auto const abs_tok =  tokenise(accept(is_char('\\')));
auto const dot_tok =  tokenise(accept(is_char('.')));
auto const start_tok = tokenise(accept(is_char('(')));
auto const end_tok = tokenise(accept(is_char(')')));
auto const let_tok = tokenise(accept_str("let"));
auto const ass_tok = tokenise(accept(is_char('=')));
auto const in_tok = tokenise(accept_str("in"));
auto const prod_tok = tokenise(accept(is_char(',')));
auto const eof_tok = name("end-of-file", tokenise(accept(is_char(EOF))));
    
parser_handle<term_expression*> parse_exp(return_app &app, return_abs &abs,
    return_let &let, return_var &var, return_num &num,
    parser_handle<term_expression*> expr
) {
    return discard(attempt(start_tok))
            && strict("error parsing subexpression"
            , log("exp", expr && discard(end_tok)))
        || log("abs", discard(attempt(abs_tok))
            && strict("error parsing abstraction"
            , all(abs, name_tok, discard(dot_tok) && expr)))
        || log("let", discard(attempt(let_tok))
            && strict("error parsing let"
            , all(let, name_tok, discard(ass_tok) && expr, discard(in_tok) && expr)))
        || log("var", all(var, attempt(name_tok)))
        || log("num", all(num, attempt(num_tok)));
}

class term_parser {
    pstream in;
    return_app app;
    return_abs abs;
    return_let let;
    return_var var;
    return_num num;

public:
    term_parser(ast_factory &ast, istream &fs)
        : in(fs), app(ast), abs(ast), let(ast), var(ast), num(ast) {}

    term_expression* operator() () {
        parser_handle<term_expression*> const expr =
            some(all(app, parse_exp(app, abs, let, var, num, reference("{expression}-", expr))));

        auto const parser = strict("error parsing expression", expr)
            && strict("unexpected trailing characters", attempt(discard(eof_tok)) || expr);

        decltype(parser)::result_type res {};

        try {
            if (!parser(in, &res)) {
                throw runtime_error("parser failed without generating an error message.");
            }
        } catch (parse_error& e) {
            stringstream err;
            err << e;
            throw runtime_error(err.str());
        }

        return res;
    }
};
        
//----------------------------------------------------------------------------
// Instantiate Type in Monomorphic Environment

class type_instantiate : public type_visitor {
    typedef map<type_expression*, type_expression*> type_map_type;

    ast_factory& ast;

    type_map_type tapp_map;
    type_map_type tvar_map;
    type_expression *exp;

public:
    virtual void visit(type_literal *const t) override {
        exp = t;
    }

    virtual void visit(type_variable *const t) override {
        type_map_type::iterator const i = tvar_map.find(t);
        if (i == tvar_map.end()) { // fresh type variable
            type_variable *const n = ast.new_type_variable();
            tvar_map[t] = n;
            exp = n;
        } else { // var in local scope
            exp = i->second;
        }
    }

    virtual void visit(type_application *const t) override {
        type_map_type::iterator const i = tapp_map.find(t);
        if (i == tapp_map.end()) { 
            type_application *const n = ast.new_type_application(nullptr, nullptr);
            tapp_map[t] = n;
            find(t->dom)->accept(this);
            n->dom = exp;
            find(t->cod)->accept(this);
            n->cod = exp;
            exp = n;
        } else {
            exp = i->second;
        }
    }

    virtual void visit(type_product *const t) override {
        find(t->left)->accept(this);
        type_expression *const left = exp;
        find(t->right)->accept(this);
        exp = ast.new_type_product(left, exp);
    }

    explicit type_instantiate(ast_factory& ast) : ast(ast) {}

    type_expression* operator() (type_expression *const t) {
        find(t)->accept(this);
        return exp;
    }
};

class typing_instantiate {
    type_instantiate inst;

public:
    typing_instantiate(ast_factory &ast) : inst(ast) {}

    typing_type operator() (typing_type ty) {
        mono_env_type env;
        for (auto const& v : ty.first) {
            env.insert(make_pair(v.first, inst(v.second)));
        }
        return make_pair(env, inst(ty.second));
    }
};

//----------------------------------------------------------------------------
// Type Graph Unification

struct unification_error : public runtime_error {
    type_expression *t1, *t2;
    unification_error(type_expression *t1, type_expression *t2)
        : runtime_error("unification error"), t1(t1), t2(t2) {}
};

class type_unify : public type_visitor {
    typedef pair<type_expression*, type_expression*> texp_pair;
    type_expression *u2;
    type_show *show_type;

    set<texp_pair> done;
    vector<texp_pair> todo;
    
    inline void mark_done(type_expression *t1, type_expression *t2) {
        done.emplace(move(make_pair(t1, t2)));
    }

    inline void queue(type_expression *t1, type_expression *t2) {
        if (t1 != t2) {
            todo.emplace_back(move(make_pair(t1, t2)));
        }
    }

public:
    class literal_unify : public type_visitor { 
        type_unify &unify;
        type_literal *t1;
    public:
        virtual void visit(type_literal *t2) override {
            unify.mark_done(t1, t2);
            if (t1->name != t2->name) {
                throw unification_error(t1, t2);
            }
            int s1 = t1->params.size();
            if (s1 != t2->params.size()) {
                throw unification_error(t1, t2);
            } else {
                row_type::const_iterator f1 = t1->params.begin();
                row_type::const_iterator f2 = t2->params.begin();
                for (int i = s1; i > 0; --i) {
                    unify.queue(*(f1++), *(f2++));
                }
            }
        }
        virtual void visit(type_variable *t2) override {
            t2->replace_with(t1);
        }
        virtual void visit(type_application *t2) override {
            throw unification_error(t1, t2);
        }
        virtual void visit(type_product *t2) override {
            throw unification_error(t1, t2);
        }
        literal_unify(type_unify &unify) : unify(unify) {}
        void operator() (type_literal *l1, type_expression *l2) {
            t1 = l1;
            l2->accept(this);
        }
    } literal;
            
    class variable_unify : public type_visitor {
        type_variable *t1;
    public:
        virtual void visit(type_literal *t2) override {
            t1->replace_with(t2);
        }
        virtual void visit(type_variable *t2) override {
            link(t1, t2);
        }
        virtual void visit(type_application *t2) override {
            t1->replace_with(t2);
        }
        virtual void visit(type_product *t2) override {
            t1->replace_with(t2);
        }
        void operator() (type_variable *v1, type_expression *v2) {
            t1 = v1;
            v2->accept(this);
        }
    } variable;

    class application_unify : public type_visitor {
        type_unify &unify;
        type_application *t1;
    public:
        virtual void visit(type_literal *t2) override {
            throw unification_error(t1, t2);
        }
        virtual void visit(type_variable *t2) override {
            t2->replace_with(t1);
        }
        virtual void visit(type_application *t2) override {
            unify.mark_done(t1, t2);
            unify.queue(t1->dom, t2->dom);
            unify.queue(t1->cod, t2->cod);
        }
        virtual void visit(type_product *t2) override {
            throw unification_error(t1, t2);
        }
        explicit application_unify(type_unify &unify) : unify(unify) {}
        void operator() (type_application *a1, type_expression *a2) {
            t1 = a1;
            a2->accept(this);
        }
    } application;

    class product_unify : public type_visitor {
        type_unify &unify;
        type_product *t1;
    public:
        virtual void visit(type_literal *t2) override {
            throw unification_error(t1, t2);
        }
        virtual void visit(type_variable *t2) override {
            t2->replace_with(t1);
        }
        virtual void visit(type_application *t2) override {
            throw unification_error(t1, t2);
        }
        virtual void visit(type_product *t2) override {
            unify.mark_done(t1, t2);
            unify.queue(t1->left, t2->left);
            unify.queue(t1->right, t2->right);
        }
        explicit product_unify(type_unify &unify) : unify(unify) {}
        void operator() (type_product *a1, type_expression *a2) {
            t1 = a1;
            a2->accept(this);
        }
    } product;

    virtual void visit(type_literal *u1) override {
        literal(u1, u2);
    }

    virtual void visit(type_variable *u1) override {
        variable(u1, u2);
    }

    virtual void visit(type_application *u1) override {
        application(u1, u2);
    }

    virtual void visit(type_product *u1) override {
        product(u1, u2);
    }

    explicit type_unify(type_show *show_type = nullptr) : literal(*this)
    , application(*this)
    , product(*this)
    , show_type(show_type)
    {}

    void unify(type_expression *t1, type_expression *t2) {
        queue(t1, t2);

        while (todo.size() > 0) {
            texp_pair tt = todo.back();
            todo.pop_back();
            type_expression *u1 = find(tt.first);
            u2 = find(tt.second);
            if ((u1 != u2) && (done.count(move(make_pair(u1, u2))) == 0)) {
                u1->accept(this);
            }
        }
    }
        
    void operator() (type_expression *t1, type_expression *t2) {
        profile<type_unify> p;
        done.clear();
        unify(t1, t2);
    }
};

//----------------------------------------------------------------------------
// Type Inference: Compositional Typings

struct inference_error : public runtime_error {
    unification_error err;
    term_expression *term;
    inference_error(unification_error &&err, term_expression *term)
        : runtime_error("inference error"), err(move(err)), term(term) {}
};

class type_inference_c: public term_visitor {
    typedef map<string, type_expression*> tycon_type;

    ast_factory& ast;
    type_show show_type;
    type_unify unify_types;

    void abstract(string const& name, typing_type const& body, typing_type& typing) {
        typing_instantiate inst(ast);
        typing = inst(body);

        mono_env_type::iterator f {typing.first.lower_bound(name)};
        mono_env_type::iterator const l {typing.first.upper_bound(name)};

        type_expression *a = ast.new_type_variable();
        if (f != l) {
            while (f != l) {
                unify_types(a, (f++)->second);
            }
            typing.first.erase(name);
        }
        typing.second = ast.new_type_application(a, typing.second);
    }

    void apply(typing_type const& fun, typing_type const& arg, typing_type& typing) {
        typing_instantiate inst(ast);
        typing_type a = inst(arg);
        typing_type f = inst(fun);

        typing.first = f.first;
        typing.first.insert(a.first.begin(), a.first.end());
        typing.second = ast.new_type_variable();
        unify_types(f.second, ast.new_type_application(a.second, typing.second));
    }

public:
    tycon_type tycons;

    type_expression *const literal_int = ast.new_type_literal("Int");
    type_expression *const literal_bool = ast.new_type_literal("Bool");

    virtual void visit(term_literal *t) override {
        t->typing.second = literal_int;
    }
    
    virtual void visit(term_variable *t) override {
        tycon_type::const_iterator j(tycons.find(t->name));
        if (j == tycons.end()) {
            type_expression *beta = ast.new_type_variable();
            t->typing.first.insert(make_pair(t->name, beta));
            t->typing.second = beta;
        } else {
            type_instantiate inst(ast);
            t->typing.second = inst(j->second);
        }
    }

    virtual void visit(term_abstraction *t) override {
        t->body->accept(this);

        try {
            abstract(t->name, t->body->typing, t->typing);
        } catch (unification_error& e) {
            throw inference_error(move(e), t);
        }
    }

    virtual void visit(term_application *t) override {
        t->fun->accept(this);
        t->arg->accept(this);

        try {
            apply(t->fun->typing, t->arg->typing, t->typing);
        } catch (unification_error& e) {
            throw inference_error(move(e), t);
        }
    }

    virtual void visit(term_product *t) override {
        t->lhs->accept(this);
        t->rhs->accept(this);

        t->typing.first = t->lhs->typing.first;
        t->typing.first.insert(t->rhs->typing.first.begin(), t->rhs->typing.first.end());
        t->typing.second = ast.new_type_product(t->lhs->typing.second, t->rhs->typing.second);
    }

    virtual void visit(term_let *t) override {
        t->rhs->accept(this);
        t->body->accept(this);

        typing_instantiate inst(ast);
        typing_type body = inst(t->body->typing);

        t->typing = body;
        t->typing.first.erase(t->name);
        mono_env_type::iterator f {body.first.lower_bound(t->name)};
        mono_env_type::iterator const l {body.first.upper_bound(t->name)};
        try {
            while (f != l) {
                typing_instantiate inst(ast);
                typing_type gen {inst(t->rhs->typing)};
                unify_types(gen.second, f->second);
                t->typing.first.insert(gen.first.begin(), gen.first.end());
                ++f;
            }
        } catch (unification_error& e) {
            throw inference_error(move(e), t);
        }
    }

    explicit type_inference_c(ast_factory& ast)
        : ast(ast), show_type(cout, true), unify_types(&show_type) {}
    
    void operator() (term_expression *t) {
        t->accept(this);
    }
};

//----------------------------------------------------------------------------
// Explain Type Inference

class explain: public term_visitor {
    term_show show_term;
    ostream &out;

public:
    virtual void visit(term_literal *t) override {
        out << "lit ---------------------------------------\n";
        show_term(t);
        out << "\n\n";
    }
    
    virtual void visit(term_variable *t) override {
        out << "var ---------------------------------------\n";
        show_term(t);
        out << "\n\n";
    }

    virtual void visit(term_abstraction *t) override {
        t->body->accept(this);

        show_term(t->body);
        out << "\nabs ---------------------------------------\n";
        show_term(t);
        out << "\n\n";
    }

    virtual void visit(term_application *t) override {
        t->fun->accept(this);
        t->arg->accept(this);

        show_term(t->fun);
        out << "\n";
        show_term(t->arg);
        out << "\napp ---------------------------------------\n";
        show_term(t);
        out << "\n\n";
    }

    virtual void visit(term_product *t) override {
        t->lhs->accept(this);
        t->rhs->accept(this);

        show_term(t->lhs);
        out << "\n";
        show_term(t->rhs);
        out << "\nprd ---------------------------------------\n";
        show_term(t);
        out << "\n\n";
    }

    virtual void visit(term_let *t) override {
        t->rhs->accept(this);
        t->body->accept(this);

        show_term(t->rhs);
        out << "\n";
        show_term(t->body);
        out << "\nlet ---------------------------------------\n";
        show_term(t);
        out << "\n\n";
    }

    explicit explain(ostream &out, bool debug = false) : show_term(out, debug), out(out) {}

    void operator() (term_expression *t) {
        if (t != nullptr) {
            t->accept(this);
        }
    }
};

//----------------------------------------------------------------------------

int main(int argc, char const *const *argv) {
    if (argc < 1) {
        printf("no input files.\n");
    } else {
        for (int i(1); i < argc; ++i) {
                ast_factory ast;
                type_inference_c infer_types(ast);

                infer_types.tycons["true"] = infer_types.literal_bool;
                infer_types.tycons["false"] = infer_types.literal_bool;

                //type_expression *const n = infer_types.literal_int;
                //infer_types.poly_env["inc_int"] = make_pair(m, ast.new_type_application(n, n));
                //infer_types.poly_env["add_int"] = make_pair(m, ast.new_type_application(
                //    n, ast.new_type_application(n, n)));

                term_show show_term(cout);

                fstream in(argv[i], ios_base::in);
                if (in.is_open()) {
                        term_parser parse(ast, in);
                        term_expression *exp(parse());
                        in.close();
                        show_term(exp);
                        cout << "\n";

                        try {
                            infer_types(exp);
                            (explain(cout))(exp);
                        } catch (inference_error &e) {
                            explain exp(cout, true);
                            type_show show_type(cout, true);
                            cout << e.what() << ":\n\n";
                            exp(e.term);
                            show_type(e.err.t1);
                            cout << " != ";
                            show_type(e.err.t2);
                            cout << "\n";
                        }
                }
        }
        
        cout << "profile: " << setprecision(16) << profile<type_unify>::report() << "\n";
    }
}
