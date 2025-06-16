import os
import json
import sqlite3
import argparse
import contextlib
import sqlglot
import sqlglot.expressions
from sqlglot.expressions import _to_s, Expression
from sqlglot import parse_one as parse_sql
from ETM_utils.ETM import evalquery
import tqdm
from copy import deepcopy as dc
from ETM_utils.process_sql import get_schema
import re
from ETM_utils.evaluation import evalquery as ESM

def preprocess(query: str, schema: dict) -> str:
    # Convert ` to "
    query = query.replace("`", '"')
    # If we have double quotes around something that ISN'T in the schema, interpret it as a literal instead (single quotes)
    pattern = r'"([^"]+)"'  # Matches text between double quotes
    words = re.findall(pattern, query)
    for word in words:
        replace = True
        if word.lower() in schema:
            replace = False
        for table in schema:
            if word.lower() in schema[table]['columns']:
                replace = False
        if replace:
            query = query.replace(f'"{word}"', f"'{word}'") # what if ' is in the word?

    query = re.sub(r'(?i)\bdatetime\(\)', "datetime('now')", query) # Replace datetime() with datetime('now')
        
    return query

def parseTree(sql: str) -> sqlglot.expressions.Select:
    return parse_sql(sql)

def rule100(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # select a vs select A
    original = dc(tree)
    root = tree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    if isinstance(value[i], sqlglot.expressions.Literal):
                        pass
                    else:
                        stack.append((value[i], f"{current_path}[{i}]")) 
            
            if isinstance(value, sqlglot.expressions.Literal):
                pass
            elif isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, str):
                # lowercase it
                current_node.args[key] = value.lower()

    if original != tree:
        print("Applied Rule 100")
    return tree

def rule101(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # select table.name from table vs. select name from table
    # if a selected column doesn't have a table, but there are no joins, and that column is selecting from the only table
    original = dc(tree)
    if 'from' not in tree.args:
        return tree
    def get_table(expr):
        expr = dc(expr)
        if isinstance(expr, sqlglot.expressions.Star):
            expr = sqlglot.expressions.Column(this=expr)
        if 'table' not in expr.args:
            if 'joins' not in tree.args:
                # selectname = expr.args['table'].args['this']
                if isinstance(tree.args['from'].args['this'], sqlglot.expressions.Subquery):
                    return expr
                tablename = tree.args['from'].args['this'].args['this'].args['this']
                expr.args['table'] = sqlglot.expressions.Identifier(this=tablename, quoted=False)
            else:
                # now, if there are more than one table, and the columns only exist in one of those tables, then add the table name
                tables = [tree.args['from'].args['this']]
                for join in tree.args['joins']:
                    tables.append(join.args['this'])
                tablename = None
                for table in tables:
                    if isinstance(table, sqlglot.expressions.Subquery):
                        continue
                    if 'columns' in schema[table.args['this'].args['this']]:
                        if isinstance(expr.args['this'], sqlglot.expressions.Star):
                            tablename = None
                            break
                        if expr.args['this'].args['this'] in schema[table.args['this'].args['this']]['columns']:
                            if not tablename:
                                tablename = table.args['this'].args['this']
                            else:
                                tablename = None
                                break
                if tablename:
                    expr.args['table'] = sqlglot.expressions.Identifier(this=tablename, quoted=False)

        return expr
        
    root = tree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    if isinstance(value[i], sqlglot.expressions.Column):
                        current_node.args[key][i] = get_table(value[i])
                    if isinstance(value[i], sqlglot.expressions.Star):
                        current_node.args[key][i] = get_table(value[i])
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, sqlglot.expressions.Column):
                current_node.args[key] = get_table(value)
            if isinstance(value, sqlglot.expressions.Star) and not isinstance(current_node, sqlglot.expressions.Column) and not isinstance(current_node, sqlglot.expressions.Count):
                current_node.args[key] = get_table(value)
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            
    if tree != original:
        print("Applied Rule 101")
    return tree   

    

def rule102(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # select a, b from table vs. select b, a from table
    # order the columns in expressions by name
    original = dc(tree)
    tree.args['expressions'].sort(key=lambda x: (str(type(x)), str(x)))
    if tree != original:
        print("Applied Rule 102")
    return tree

def rule103(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # select table.a from table t1 vs. select t1.a from table t1
    # anything that points to a table alias now points to the original
    original = dc(tree)
    if 'from' not in tree.args:
        return tree
    tables = [tree.args['from'].args['this']]
    if 'joins' in tree.args:
        for join in tree.args['joins']:
            tables.append(join.args['this'])
    for table in tables:
        if 'alias' in table.args:
            if table.args['alias'] == None:
                continue
            table_id = table.args['this'] # Identifier
            alias_id = table.args['alias'].args['this'] # Identifier
            # remove alias
            table.args.pop('alias')
            # loop through entire tree, look for all identifiers. If the identifier is the same as the alias, replace it with the table.
            root = tree
            stack = [(root, "")]  # Stack contains tuples of (current_node, path)
            results = []  # To store the traversal paths and leaf values
            while stack:
                current_node, path = stack.pop()
                for key, value in current_node.args.items():
                    current_path = f"{path}/{key}" if path else key
                    if isinstance(value, sqlglot.expressions.TableAlias):
                        # skip
                        continue
                    if isinstance(value, list):
                        for i in range(len(value)):
                            stack.append((value[i], f"{current_path}[{i}]")) 
                    if isinstance(value, Expression):
                        # If the value is an Expression node, add it to the stack
                        stack.append((value, current_path))
                    if isinstance(value, sqlglot.expressions.Identifier):
                        if value == alias_id:
                            current_node.args[key] = table_id
                    

    if tree != original:
        print("Applied Rule 103")
    return tree

def rule104(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # select a from table1 join table2 vs. select a from table2 join table1
    # order the joins by table name
    original = dc(tree)

    if 'from' not in tree.args:
        return tree
    initial_table = tree.args['from'].args['this']
    tables = [initial_table]

    ons = []
    # ons = {}
    if 'joins' in tree.args:
        for join in tree.args['joins']:
            if 'side' in join.args:
                return tree
            tables.append(join.args['this'])
            if 'on' in join.args:
                ons.append(join.args['on'])
                # ons[join.args['this']] = join.args['on']
    else:
        return tree

    tables.sort(key=lambda x: (str(type(x)), str(x)))
    ons.sort(key=lambda x: (str(type(x)), str(x)))
    
    tree.args['from'].args['this'] = tables[0]
    # combine ons into one big and statement
    if ons:
        combined = ons[0]
        for on in ons[1:]:
            combined = sqlglot.expressions.And(this=combined, expression=on)
    else:
        combined = 1
    ons = [combined]
    
    joins = []
    while(len(ons) < len(tables) - 1):
        ons.append(1)
    for table, on in zip(tables[1:],ons):
        if on == 1:
            join = sqlglot.expressions.Join(this=table)
        else:
            join = sqlglot.expressions.Join(this=table, on=on)
        joins.append(join)
    tree.args['joins'] = joins
    if tree != original:
        print("Applied Rule 104")
    return tree

def rule105(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # a =/and/or b vs b =/and/or a
    # order all equality, ands, and ors
    original = dc(tree)
    root = tree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values

    def sort(node):
        if isinstance(node, sqlglot.expressions.EQ) or isinstance(node, sqlglot.expressions.And) or isinstance(node, sqlglot.expressions.Or):
            vals = [node.args['this'],node.args['expression']]
            # first, ensure the children are not of the same type
            while any([isinstance(val, type(node)) for val in vals]):
                for i in range(len(vals)):
                    if isinstance(vals[i], type(node)):
                        vals[i] = [vals[i].args['this'], vals[i].args['expression']]
                        vals = vals[0:i] + vals[i] + vals[i+1:]
            
            vals.sort(key=lambda x: (str(type(x)), str(x)))
            # REBUILD
            it = iter(vals)
            result = next(it)  # Start with the first element
            
            for expr in it:
                result = type(node)(this=result, expression=expr)
            
            node = result
                

        return node
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    current_node.args[key][i] = sort(value[i])
                    stack.append((current_node.args[key][i], f"{current_path}[{i}]")) 
            
            current_node.args[key] = sort(value)

            if isinstance(current_node.args[key], Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((current_node.args[key], current_path))


    if tree != original:
        print("Applied Rule 105")
    return tree

def rule106(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # select a as b vs. select a
# all Aliases are removed (and their references are replaced with the original)
    original = dc(tree)
    def removeAlias(alias: sqlglot.expressions.Alias):
        alias_id = alias.args['alias']
        alias = alias.args['this']

        # loop through entire tree, look for all identifiers. If the identifier is the same as the alias, replace it with the table.
        root = tree
        stack = [(root, "")]
        results = []
        while stack:
            current_node, path = stack.pop()
            for key, value in current_node.args.items():
                current_path = f"{path}/{key}" if path else key
                if isinstance(value, sqlglot.expressions.Alias):
                    if value.args['this'] == alias:
                        value = value.args['this']
                    continue
                if isinstance(value, list):
                    for i in range(len(value)):
                        if isinstance(value[i], sqlglot.expressions.Alias):
                            if value[i].args['this'] == alias:
                                value[i] = value[i].args['this']
                            current_node.args[key][i] = value[i]
                        else:
                            stack.append((value[i], f"{current_path}[{i}]")) 
                if isinstance(value, Expression):
                    # If the value is an Expression node, add it to the stack
                    stack.append((value, current_path))
                if isinstance(value, sqlglot.expressions.Identifier):
                    if value == alias_id:
                        current_node.args[key] = alias
    root = tree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    if isinstance(value[i], sqlglot.expressions.Alias):
                        # remove it
                        removeAlias(value[i])
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, sqlglot.expressions.Alias):
                # remove it
                removeAlias(value)
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            
    if tree != original:
        print("Applied Rule 106")
    return tree
def rule107(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # (a) vs. a
    # remove parentheses around 1 operation
    original = dc(tree)
    root = tree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    if isinstance(value[i], sqlglot.expressions.Paren):
                        if len(value[i].args) == 1:
                            current_node.args[key][i] = value[i].args['this']
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, sqlglot.expressions.Paren):
               if len(value.args) == 1:
                   current_node.args[key] = value.args['this']

    if tree != original:
        print("Applied Rule 107")
    return tree



def rule108(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # "table" vs. table
    original = dc(tree)
    root = tree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, sqlglot.expressions.Identifier):
                # try to convert to real
                pass
                if value.args['quoted'] == True:
                    value.args['quoted'] = False
                    current_node.args[key] = value

    if tree != original:
        print("Applied Rule 108")
    return tree


def rule1(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # where c1 = (select min/max(c1) from t) vs. order by c1 asc/desc limit 1
    original = dc(tree)
    if 'order' in tree.args: # If there already is an order, this rule doesn't apply
        return tree
    if 'where' not in tree.args:
        return tree
    if 'limit' in tree.args:
        limit = tree.args['limit']
        if limit != None:
            return tree
    
    condition = tree.args['where']
    root = condition
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, sqlglot.expressions.EQ):
                
                if isinstance(value.args['expression'], sqlglot.expressions.Subquery) or isinstance(value.args['this'], sqlglot.expressions.Subquery):
                    
                    if isinstance(value.args['expression'], sqlglot.expressions.Subquery):
                        subquery = value.args['expression']
                        col = value.args['this']
                    else:
                        subquery = value.args['this']
                        col = value.args['expression']
                    if 'this' not in subquery.args:
                        continue
                    
                    select = subquery.args['this']
                    if 'expressions' not in select.args:
                        continue
                    
                    if len(select.args['expressions']) != 1:
                        continue
                    if 'from' not in select.args:
                        continue
                    if 'joins' in select.args:
                        continue
                    
                    ex = select.args['expressions'][0]
                    if not isinstance(ex, sqlglot.expressions.Max) and not isinstance(ex, sqlglot.expressions.Min):
                        continue
                    if 'this' not in ex.args:
                        continue
                    
                    if 'table' not in col.args:
                        continue
                    
                    if 'this' not in col.args:
                        continue
                    
                    if ex.args['this'] != col:
                        continue
                    
                    col_table_name = col.args['table'].args['this']
                    col_name = col.args['this'].args['this']
                    if isinstance(col_table_name, sqlglot.expressions.Select):
                        continue
                    if col_name not in schema[col_table_name]['unique']:
                        continue
                    
                    # If we reach here, we can apply the rule
                    if isinstance(ex, sqlglot.expressions.Min):
                        tree.args['order'] = sqlglot.expressions.Order(expressions=[sqlglot.expressions.Ordered(this=col, desc = False)])
                    else:
                        tree.args['order'] = sqlglot.expressions.Order(expressions=[sqlglot.expressions.Ordered(this=col, desc = True)])
                    tree.args['limit'] = sqlglot.expressions.Limit(expression=sqlglot.expressions.Literal(this="1.0", is_string=False))
                    current_node.args[key] = sqlglot.expressions.EQ(this=sqlglot.expressions.Literal(this="1.0", is_string=False), expression=sqlglot.expressions.Literal(this="1.0", is_string=False))
    if original != tree:
        print("Applied Rule 1")
    return tree

def rule2(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # distinct c1 vs c1: only if c1 is unique
    original = dc(tree)
    if 'distinct' in tree.args:
        if 'joins' not in tree.args:
            if 'expressions' in tree.args:
                expressions = tree.args['expressions']
                for ex in expressions:
                    if isinstance(ex, sqlglot.expressions.Column):
                        if 'table' in ex.args:
                            if isinstance(ex.args['table'], sqlglot.expressions.Select):
                                continue
                            if not isinstance(ex.args['table'].args['this'], sqlglot.expressions.Select):
                                col_table_name = ex.args['table'].args['this']
                                if not isinstance(ex.args['this'], sqlglot.expressions.Star):
                                    col_name = ex.args['this'].args['this']
                                    if col_name in schema[col_table_name]['unique']:
                                        # rule can be applied
                                        tree.args.pop('distinct')
                                        break
    def process_distinct(dist: sqlglot.expressions.Distinct):
        if 'expressions' not in dist.args:
            return dist
        if len(dist.args['expressions']) != 1:
            return dist
        col = dist.args['expressions'][0]
        if not isinstance(col, sqlglot.expressions.Column):
            return dist
        if 'this' not in col.args['table'].args:
            return dist
        col_table_name = col.args['table'].args['this']
        col_name = col.args['this'].args['this']
        if 'joins' in tree.args:
            return dist
        if col_name in schema[col_table_name]['unique']:
            # rule can be applied
            return col
        return dist
    root = tree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    if isinstance(value[i], sqlglot.expressions.Distinct):
                        current_node.args[key][i] = process_distinct(value[i])
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, sqlglot.expressions.Distinct):
                current_node.args[key] = process_distinct(value)

    if original != tree:
        print("Applied Rule 2")
    return tree

def rule4(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # group by c1 vs. group by c1, c2, c3: only if c1 is unique
    original = dc(tree)
    if 'group' not in tree.args:
        return tree
    if 'order' in tree.args: # If there is an order, this rule doesn't apply
        return tree
    expressions = tree.args['group'].args['expressions']
    new_expressions = []
    for ex in expressions:
        if isinstance(ex, sqlglot.expressions.Column):
            if 'table' in ex.args:
                col_table_name = ex.args['table'].args['this']
                col_name = ex.args['this'].args['this']
                if not isinstance(col_table_name, sqlglot.expressions.Select):
                    if col_name in schema[col_table_name]['unique']:
                        new_expressions = [ex]
                        break
        new_expressions.append(ex)
    tree.args['group'].args['expressions'] = new_expressions
    

    if original != tree:
        print("Applied Rule 4")
    return tree

def rule6(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # count(*) vs. count(c1): only if c1 is non_null
    original = dc(tree)
    root = tree
    def process_count(count: sqlglot.expressions.Count):
        count_col = count.args['this']
        if not isinstance(count_col, sqlglot.expressions.Column):
            return count
        if 'table' not in count_col.args:
            return count
        if isinstance(count_col.args['table'], sqlglot.expressions.Select):
            return count
        col_table_name = count_col.args['table'].args['this']
        col_name = count_col.args['this'].args['this']
        if isinstance(col_table_name, sqlglot.expressions.Select):
            return count
        if col_name in schema[col_table_name]['non_null']:
            newcount = sqlglot.expressions.Count(this=sqlglot.expressions.Star(), big_int=True)
            return newcount
        return count
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    if isinstance(value[i], sqlglot.expressions.Count):
                        current_node.args[key][i] = process_count(value[i])
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, sqlglot.expressions.Count):
                current_node.args[key] = process_count(value)


    if original != tree:
        print("Applied Rule 6")
    return tree 

def rule7(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # where c1 is not null vs. nothing: only if c1 is non_null
    original = dc(tree)
    if 'where' not in tree.args:
        return tree
    def process_not(not_clause: sqlglot.expressions.Not):
        
        is_clause = not_clause.args['this']
        
        if not isinstance(is_clause, sqlglot.expressions.Is): # If it's not an Is, this rule doesn't apply
            return not_clause
        
        is_col = is_clause.args['this']
        if not isinstance(is_col, sqlglot.expressions.Column): # If it's not a Column, this rule doesn't apply
            return not_clause
        if 'expression' not in is_clause.args:
            return not_clause
        if not isinstance(is_clause.args['expression'], sqlglot.expressions.Null): # If it's not a Null, this rule doesn't apply
            return not_clause
        
        col_table_name = is_col.args['table'].args['this']
        col_name = is_col.args['this'].args['this']
        if col_name not in schema[col_table_name]['non_null']: # If the column is nullable, this rule doesn't apply
            return not_clause
        
        # If we reach here, we can apply the rule
        new_clause = sqlglot.expressions.EQ(this=sqlglot.expressions.Literal(this="1.0", is_string=False), expression=sqlglot.expressions.Literal(this="1.0", is_string=False))
        return new_clause
    condition = tree.args['where']
    root = condition
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, sqlglot.expressions.Subquery):
                continue
            if isinstance(value, list):
                for i in range(len(value)):
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, sqlglot.expressions.Not):
                current_node.args[key] = process_not(value)




    
    
    if original != tree:
        print("Applied Rule 7")
    return tree


def rule8(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # cast(sum(c) as float) / count(*) vs. avg(c) -> only if c is non_null
    original = dc(tree)
    root = tree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    def substituteDivForAvg(node: sqlglot.expressions.Div) -> Expression:

        if 'this' not in node.args:
            return node
        if 'expression' not in node.args:
            return node
        cast = node.args['this']
        if not isinstance(cast, sqlglot.expressions.Cast):
            return node
        if 'this' not in cast.args:
            return node
        summer = cast.args['this']
        if 'to' not in cast.args:
            return node
        to = cast.args['to']
        if not isinstance(to, sqlglot.expressions.DataType):
            return node
        if not isinstance(summer, sqlglot.expressions.Sum):
            return node
        if 'this' not in summer.args:
            return node
        col = summer.args['this']
        if not isinstance(col, sqlglot.expressions.Column):
            return node
        dtype = to.args['this'] # enum 'Type'
        if dtype.name != "FLOAT":
            return node
        exp = node.args['expression']
        if not isinstance(exp, sqlglot.expressions.Count):
            return node
        if 'this' not in exp.args:
            return node
        star = exp.args['this']
        if not isinstance(star, sqlglot.expressions.Star):
            return node
        # check if c is non_null
        if 'table' not in col.args:
            return node
        if 'this' not in col.args:
            return node
        table_name = col.args['table'].args['this']
        col_name = col.args['this'].args['this']
        if col_name not in schema[table_name]['non_null']:
            return node

        # if we get here, we can apply the rule

        return sqlglot.expressions.Avg(this=col)
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    if isinstance(value[i], sqlglot.expressions.Div):
                        value[i] = substituteDivForAvg(value[i])
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, sqlglot.expressions.Div):
                current_node.args[key] = substituteDivForAvg(value)

    if original != tree:
        print("Applied Rule 8")
    return tree 

def rule9(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # count(case when cond then 1/col else null end) vs. sum(case when cond then 1 else 0 end) -> only if col is non_null
    original = dc(tree)
    root = tree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    def substituteCountForSum(node: sqlglot.expressions.Count) -> Expression:
        if 'this' not in node.args:
            return node
        case = node.args['this']
        if not isinstance(case, sqlglot.expressions.Case):
            return node
        
        default = case.args['default']
        if default:
            if not isinstance(default, sqlglot.expressions.Null):
                return node
        
        if 'ifs' not in case.args:
            return node
        ifs = case.args['ifs']
        if len(ifs) != 1:
            return node
        ifexp = ifs[0]
        if not isinstance(ifexp, sqlglot.expressions.If):
            return node
        if 'true' not in ifexp.args:
            return node
        true = ifexp.args['true']
        if not (isinstance(true, sqlglot.expressions.Literal) or isinstance(true, sqlglot.expressions.Column)):
            return node
        if isinstance(true, sqlglot.expressions.Literal):
            if 'this' not in true.args:
                return node
            if true.args['this'] != '1.0':
                return node
        if isinstance(true, sqlglot.expressions.Column):
            # column must be non_null
            if 'table' not in true.args:
                return node
            if 'this' not in true.args:
                return node
            if 'this' not in true.args['table'].args:
                return node
            if 'this' not in true.args['this'].args:
                return node
            table_name = true.args['table'].args['this']
            col_name = true.args['this'].args['this']
            if isinstance(table_name, sqlglot.expressions.Select):
                return node
            if col_name not in schema[table_name]['non_null']:
                return node
        # if we get here, we can apply the rule
        new = sqlglot.expressions.Sum()
        new.args['this'] = sqlglot.expressions.Case(ifs=[sqlglot.expressions.If(this=ifexp.args['this'], true=sqlglot.expressions.Literal(this='1.0', is_string=False))], default=sqlglot.expressions.Literal(this='0', is_string=False))
        return new
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    if isinstance(value[i], sqlglot.expressions.Count):
                        value[i] = substituteCountForSum(value[i])
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, sqlglot.expressions.Count):
                current_node.args[key] = substituteCountForSum(value)
    if original != tree:
        print("Applied Rule 9")
    return tree

def rule10(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # select min/max(a) from table vs. select a from table order by a asc/dec limit 1
    original = dc(tree)
    if 'from' not in tree.args:
        return tree
    
    if 'order' not in tree.args: # If there is no Order, this rule doesn't apply
        return tree
    order = tree.args['order']
    if 'expressions' not in order.args:
        return tree
    
    if len(order.args['expressions']) != 1:
        return tree
    order = order.args['expressions'][0]
    order_col = order.args['this']
    desc = order.args['desc']
    
    if 'limit' not in tree.args: # If there is no limit, this rule doesn't apply
        return tree
    limit = tree.args['limit']
    if limit == None: # If there is no limit, this rule doesn't apply
        return tree
    if 'expression' not in limit.args:
        return tree
    if limit.args['expression'].args['this'] != '1.0': # If the limit isn't 1, this rule doesn't apply
        return tree

    # Now, if order_col is in the select expressions, we can apply the rule
    if 'expressions' not in tree.args:
        return tree

    newexpressions = []
    for ex in tree.args['expressions']:
        if ex == order_col:
            if desc:
                ex = sqlglot.expressions.Max(this=ex)
            else:
                ex = sqlglot.expressions.Min(this=ex)
            tree.args.pop('order')
            tree.args.pop('limit')
        newexpressions.append(ex)
    tree.args['expressions'] = newexpressions

    if tree != original:
        print("Applied Rule 10")
    return tree

def rule11(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # select * vs select a, b, c, etc.
    original = dc(tree)
    if 'expressions' not in tree.args:
        return tree
    expressions = tree.args['expressions']
    new_expressions = []
    for ex in expressions:
        if isinstance(ex, sqlglot.expressions.Column):
            if isinstance(ex.args['this'],sqlglot.expressions.Star):
            
                if 'table' in ex.args:
                    # in this case, add all columns from the table
                    table = ex.args['table']
                    table_name = table.args['this']
                    for col in schema[table_name]['columns']:
                        new_ex = sqlglot.expressions.Column(this=sqlglot.expressions.Identifier(this=col,quoted=False),table = ex.args['table'])
                        new_expressions.append(new_ex)
                else:
                    # in this case, add all columns from any tables being joined
                    tables = [tree.args['from'].args['this']]
                    for join in tree.args['joins']:
                        tables.append(join.args['this'])
                    for table in tables:
                        table_name = table.args['this'].args['this']
                        for col in schema[table_name]['columns']:
                            new_ex = sqlglot.expressions.Column(this=sqlglot.expressions.Identifier(this=col,quoted=False),table = table.args['this'])
                            new_expressions.append(new_ex)
            else:
                new_expressions.append(ex)
        else:
            new_expressions.append(ex)
    # exit()
    tree.args['expressions'] = new_expressions
    if tree != original:
        print("Applied Rule 11")
    return tree

def rule12(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # 150.0 vs. 150 vs. '150' - any number not starting with 0
    # make all literal numbers reals
    original = dc(tree)
    root = tree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, sqlglot.expressions.Literal):
                # try to convert to real
                try:
                    if value.args['this'][0] != '0':
                        value.args['this'] = str(float(value.args['this']))
                        value.args['is_string'] = False
                        current_node.args[key] = value
                except:
                    pass

    if tree != original:
        print("Applied Rule 12")
    return tree

def rule13(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # from t2 where c2 in (select c1 from t1 where d) vs. from t1 join t2 on t1.c1 = t2.c2 where d
    original = dc(tree)
    if 'from' not in tree.args:
        return tree
    if 'joins' in tree.args:
        return tree
    if 'where' not in tree.args:
        return tree
    
    condition = tree.args['where'].args['this']
    if not isinstance(condition, sqlglot.expressions.In) and not isinstance(condition, sqlglot.expressions.EQ):
        return tree
    if isinstance(condition, sqlglot.expressions.In):
        eq = False
    else:
        eq = True
    outer_table = tree.args['from'].args['this']
    
    if 'this' not in condition.args:
        return tree
    if eq:
        if 'expression' not in condition.args:
            return tree
    else:
        if 'query' not in condition.args:
            return tree
    if eq:
        if not isinstance(condition.args['expression'], sqlglot.expressions.Subquery):
            return tree
        subquery = condition.args['expression']
    else:  
        if not isinstance(condition.args['query'], sqlglot.expressions.Subquery):
            return tree
        subquery = condition.args['query']
    if not isinstance(condition.args['this'], sqlglot.expressions.Column):
        return tree
    outer_col = condition.args['this']
    
    if 'this' not in subquery.args:
        return tree
    select = subquery.args['this']
    if 'this' not in outer_col.args:
        return tree
    if 'table' not in outer_col.args:
        return tree
    if 'this' not in outer_col.args['this'].args:
        return tree
    if 'this' not in outer_col.args['table'].args:
        return tree
    if 'expressions' not in select.args:
        return tree
    if 'groupby' in select.args:
        return tree
    if 'orderby' in select.args:
        return tree
    
    
    
    inner_exp = select.args['expressions']
    if len(inner_exp) != 1:
        return tree
    inner_col = inner_exp[0]
    if 'from' not in select.args:
        return tree
    table = select.args['from'].args['this']
    if isinstance(table, sqlglot.expressions.Subquery):
        return tree
    inner_table_name = table.args['this'].args['this']
    
    if 'this' not in inner_col.args:
        return tree
    if 'this' not in inner_col.args['this'].args:
        return tree
    if 'table' not in inner_col.args:
        return tree
    if 'this' not in inner_col.args['table'].args:
        return tree
    inner_col_name = inner_col.args['this'].args['this']
    # check if col is pk of table
    if inner_col_name not in schema[inner_table_name]['primary_keys']:
        return tree
    outer_table_name = outer_table.args['this'].args['this']
    outer_col_name = outer_col.args['this'].args['this']
    if outer_col_name not in schema[outer_table_name]['foreign_keys']:
        return tree
    if schema[outer_table_name]['foreign_keys'][outer_col_name] != f"{inner_table_name}.{inner_col_name}":
        return tree
    if 'where' in select.args:
        where = select.args['where'].args['this']
        if eq:
            # in this case, where must be an eq, and it must be on a unique column
            if not isinstance(where, sqlglot.expressions.EQ):
                return tree
            if 'this' not in where.args:
                return tree
            if 'expression' not in where.args:
                return tree
            if not isinstance(where.args['this'], sqlglot.expressions.Column):
                return tree
            col = where.args['this']
            if 'table' not in col.args:
                return tree
            if 'this' not in col.args:
                return tree
            col_table_name = col.args['table'].args['this']
            if 'this' not in col.args['this'].args:
                return tree
            col_name = col.args['this'].args['this']
            if col_name not in schema[col_table_name]['unique']:
                return tree
    else:
        if eq:
            return tree
        where = sqlglot.expressions.EQ(this=sqlglot.expressions.Literal(this="1.0", is_string=False), expression=sqlglot.expressions.Literal(this="1.0", is_string=False))
    # if we reach here, we can apply the rule
    tree.args['where'].args['this'] = where
    tree.args['joins'] = [sqlglot.expressions.Join(this=table, on=sqlglot.expressions.EQ(this=sqlglot.expressions.Column(this=sqlglot.expressions.Identifier(this=inner_col_name,quoted=False),table=sqlglot.expressions.Identifier(this=inner_table_name,quoted=False)),expression=sqlglot.expressions.Column(this=sqlglot.expressions.Identifier(this=outer_col_name,quoted=False),table=sqlglot.expressions.Identifier(this=outer_table_name,quoted=False))))]
    if original != tree:
        print("Applied Rule 13")
    return tree
def rule14(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # select X from t1 join t2 on t1.c1 = t2.c2 vs. select X from t2: only if c1 is a primary key in t1 and c2 is a foreign key in t2 referencing c1. c1 must be noncomposite and X can be any columns from t2
    original = dc(tree)
    if 'from' not in tree.args:
        return tree
    if 'joins' not in tree.args:
        return tree
    if 'expressions' not in tree.args:
        return tree
    joins = tree.args['joins']
    # get all ons
    eqs = []
    for join in joins:
        if 'side' in join.args:
            return tree
        if 'on' in join.args:
            on = join.args['on']
            if isinstance(on, sqlglot.expressions.And):
                eqs = []
                stack = [on]
                while stack:
                    current = stack.pop()
                    if isinstance(current, sqlglot.expressions.EQ):
                        eqs.append(current)
                    elif isinstance(current, sqlglot.expressions.And):
                        stack.append(current.args['this'])
                        stack.append(current.args['expression'])
            else:
                eqs.append(on)
    remove = []
    for eq in eqs:
        if 'this' not in eq.args:
            continue
        if 'expression' not in eq.args:
            continue
        val1 = eq.args['this']
        val2 = eq.args['expression']
        if not isinstance(val1, sqlglot.expressions.Column):
            continue
        if not isinstance(val2, sqlglot.expressions.Column):
            continue
        if 'table' not in val1.args:
            continue
        if 'table' not in val2.args:
            continue
        if 'this' not in val1.args['table'].args:
            continue
        if 'this' not in val2.args['table'].args:
            continue
        if isinstance(val1.args['table'].args['this'], sqlglot.expressions.Select):
            continue
        if isinstance(val2.args['table'].args['this'], sqlglot.expressions.Select):
            continue
        
        table1 = val1.args['table'].args['this']
        table2 = val2.args['table'].args['this']
        if 'this' not in val1.args:
            continue
        if 'this' not in val2.args:
            continue
        
        col1 = val1.args['this'].args['this']
        col2 = val2.args['this'].args['this']
        pair = False
        if col1 in schema[table1]['primary_keys']:
            if col2 in schema[table2]['foreign_keys']:        
                if schema[table2]['foreign_keys'][col2] == f"{table1}.{col1}":
                    foreign_table = table2
                    foreign_col = col2
                    primary_table = table1
                    primary_col = col1
                    pair = True
        if not pair:
            
            if col2 in schema[table2]['primary_keys']:         
                if col1 in schema[table1]['foreign_keys']:
                    if schema[table1]['foreign_keys'][col1] == f"{table2}.{col2}":
                        foreign_table = table1
                        foreign_col = col1
                        primary_table = table2
                        primary_col = col2
                        pair = True
        
        if not pair:
            continue
        # now, check if pk is non-composite
        if len(schema[primary_table]['primary_keys']) > 1:
            continue
        # Now, we need to check the tree. If it contain columns from the primary table besides the primary key, we can't apply the rule
        def isValid(tree: sqlglot.expressions.Expression, pktable: str, pkcol: str) -> bool:
            # given a tree, does it contain any columns from the primary table besides the primary key?
            root = tree
            stack = [(root, "")]  # Stack contains tuples of (current_node, path)
            results = []  # To store the traversal paths and leaf values
            while stack:
                current_node, path = stack.pop()
                for key, value in current_node.args.items():
                    current_path = f"{path}/{key}" if path else key
                    if isinstance(value, sqlglot.expressions.Select):
                        continue
                    if isinstance(value, list):
                        for i in range(len(value)):
                            if isinstance(value[i], sqlglot.expressions.Column):
                                if 'table' in value[i].args:
                                    if 'this' in value[i].args['table'].args:
                                        if value[i].args['table'].args['this'] == pktable:
                                            if 'this' in value[i].args['this'].args:
                                                if value[i].args['this'].args['this'] != pkcol:
                                                    return False
                                            else:
                                                return False
                            stack.append((value[i], f"{current_path}[{i}]")) 
                    if isinstance(value, Expression):
                        # If the value is an Expression node, add it to the stack
                        stack.append((value, current_path))
                    if isinstance(value, sqlglot.expressions.Column):
                        if 'table' in value.args:
                            if 'this' in value.args['table'].args:
                                if value.args['table'].args['this'] == pktable:
                                    if 'this' in value.args['this'].args:
                                        if value.args['this'].args['this'] != pkcol:
                                            return False
                                    else:
                                        return False
            return True
        if not isValid(tree, primary_table, primary_col):
            continue
        # Now, we can apply the rule
        # First, note which table and eq to remove
        remove.append((sqlglot.expressions.Table(this=sqlglot.expressions.Identifier(this=primary_table,quoted=False)),eq, {"primary_table": primary_table, "foreign_table": foreign_table, "primary_col": primary_col, "foreign_col": foreign_col}))
    if remove:
        for r in remove:
            table, eq, data = r
            primary_table = data['primary_table']
            foreign_table = data['foreign_table']
            primary_col = data['primary_col']
            foreign_col = data['foreign_col']
            
            # get a list of all tables in the join
            tables = [tree.args['from'].args['this']]
            for join in tree.args['joins']:
                tables.append(join.args['this'])
            if table not in tables:
                continue
            tables.remove(table)
            eqs.remove(eq)
            # rebuild the join
            if len(tables) == 1:
                tree.args['from'].args['this'] = tables[0]
                tree.args['joins'] = []
            else:
                if len(eqs) == 1:
                    on = eqs[0]
                if len(eqs) == 0:
                    on = sqlglot.expressions.EQ(this=sqlglot.expressions.Literal(this="1.0", is_string=False), expression=sqlglot.expressions.Literal(this="1.0", is_string=False))
                if len(eqs) > 1:
                    it = iter(eqs)
                    on = next(it)
                    for eq in it:
                        on = sqlglot.expressions.And(this=on, expression=eq)
                tree.args['from'].args['this'] = tables[0]
                tree.args['joins'] = [sqlglot.expressions.Join(this=tables[1], on=on)]
                if len(tables) > 2:
                    for t in tables[2:]:
                        tree.args['joins'].append(sqlglot.expressions.Join(this=t))
            # Now, replace all instances of the primary key with the foreign key
            root = tree
            stack = [(root, "")]  # Stack contains tuples of (current_node, path)
            results = []  # To store the traversal paths and leaf values
            while stack:
                current_node, path = stack.pop()
                for key, value in current_node.args.items():
                    current_path = f"{path}/{key}" if path else key
                    if isinstance(value, list):
                        for i in range(len(value)):
                            if isinstance(value[i], sqlglot.expressions.Column):
                                if 'table' in value[i].args:
                                    if 'this' in value[i].args['table'].args:
                                        if value[i].args['table'].args['this'] == primary_table:
                                            if 'this' in value[i].args['this'].args:
                                                if value[i].args['this'].args['this'] == primary_col:
                                                    value[i] = sqlglot.expressions.Column(this=sqlglot.expressions.Identifier(this=foreign_col,quoted=False),table = sqlglot.expressions.Identifier(this=foreign_table,quoted=False))
                            stack.append((value[i], f"{current_path}[{i}]")) 
                    if isinstance(value, Expression):
                        # If the value is an Expression node, add it to the stack
                        stack.append((value, current_path))
                    if isinstance(value, sqlglot.expressions.Column):
                        if 'table' in value.args:
                            if 'this' in value.args['table'].args:
                                if value.args['table'].args['this'] == primary_table:
                                    if 'this' in value.args['this'].args:
                                        if value.args['this'].args['this'] == primary_col:
                                            current_node.args[key] = sqlglot.expressions.Column(this=sqlglot.expressions.Identifier(this=foreign_col,quoted=False),table = sqlglot.expressions.Identifier(this=foreign_table,quoted=False))

    if original != tree:
        print("Applied Rule 14")
    return tree

def rule15 (tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # sbstr(c1, a, b) = x and sbstr(c1, c, d) between y and z vs. c1 between xy and xz
    original = dc(tree)
    root = tree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    def extract_ands(and_node: sqlglot.expressions.And) -> list:
        ands = []
        stack = [and_node]
        while stack:
            current = stack.pop()
            for key, value in current.args.items():
                if isinstance(value, sqlglot.expressions.And):
                    stack.append(value)
                elif isinstance(value, Expression):
                    ands.append(value)
        return ands
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, sqlglot.expressions.And):
                # get all ands that are nested
                ands = extract_ands(value)
                ands_with_substr = []
                newands = []
                
                for and_node in ands:
                    if isinstance(and_node, sqlglot.expressions.EQ) or isinstance(and_node, sqlglot.expressions.GTE) or isinstance(and_node, sqlglot.expressions.LTE) or isinstance(and_node, sqlglot.expressions.GT) or isinstance(and_node, sqlglot.expressions.LT):
                        val1 = and_node.args['this']
                        val2 = and_node.args['expression']
                        if isinstance(val1, sqlglot.expressions.Substring) or isinstance(val2, sqlglot.expressions.Substring):
                            ands_with_substr.append(and_node)
                    newands.append(and_node)
                
                if len(ands_with_substr) < 2:
                    continue
                
                # Now, to apply the rule we must have one of them being eq and the other being GTE/LTE or GT/LT
                # for every eq node, see if there's a gte/lte/gt/lt that lines up with it.
                eqs = []
                for and_node in ands_with_substr:
                    if isinstance(and_node, sqlglot.expressions.EQ):
                        eqs.append(and_node)
                for eq in eqs:
                    eqval1 = eq.args['this']
                    eqval2 = eq.args['expression']
                    if isinstance(eqval1, sqlglot.expressions.Substring):
                        eqcol = eqval1.args['this']
                        eqstart = eqval1.args['start']
                        eqlength = eqval1.args['length']
                        eqlit = eqval2
                    if isinstance(eqval2, sqlglot.expressions.Substring):
                        eqcol = eqval2.args['this']
                        eqstart = eqval2.args['start']
                        eqlength = eqval2.args['length']
                        eqlit = eqval1
                    
                    for node in ands_with_substr:
                        
                        if isinstance(node, sqlglot.expressions.GTE) or isinstance(node, sqlglot.expressions.LTE) or isinstance(node, sqlglot.expressions.GT) or isinstance(node, sqlglot.expressions.LT):
                            
                            v1 = node.args['this']
                            v2 = node.args['expression']
                            if isinstance(v1, sqlglot.expressions.Substring):
                                col = v1.args['this']
                                start = v1.args['start']
                                length = v1.args['length']
                                lit = v2
                            elif isinstance(v2, sqlglot.expressions.Substring):
                                col = v2.args['this']
                                start = v2.args['start']
                                length = v2.args['length']
                                lit = v1
                            else:
                                continue
                            if col == eqcol:
                                if float(eqstart.args['this']) == 1.0:
                                    if float(eqstart.args['this']) + float(eqlength.args['this']) == float(start.args['this']):
                                        match type(node):
                                            case sqlglot.expressions.GTE:
                                                new = sqlglot.expressions.GTE()
                                            case sqlglot.expressions.LTE:
                                                new = sqlglot.expressions.LTE()
                                            case sqlglot.expressions.GT:
                                                new = sqlglot.expressions.GT()
                                            case sqlglot.expressions.LT:
                                                new = sqlglot.expressions.LT()
                                            case _:
                                                new = None
                                        
                                        new.args['this'] = col
                                        if eqlit.args['this'][-2:] == '.0':
                                            eqlit.args['this'] = eqlit.args['this'][:-2]
                                        if lit.args['this'][-2:] == '.0':
                                            lit.args['this'] = lit.args['this'][:-2]
                                        new.args['expression'] = sqlglot.expressions.Literal(this=f"{eqlit.args['this']}{lit.args['this']}", is_string=True)
                                        newands.append(new)
                                        if eq in newands:
                                            newands.remove(eq)
                                        if node in newands:
                                            newands.remove(node)
                # build up the new and statement
                if newands:
                    new = newands[0]
                    for node in newands[1:]:
                        new = sqlglot.expressions.And(this=new, expression=node)
                    current_node.args[key] = new

    if original != tree:
        print("Applied Rule 15")
    return tree

def rule16(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # a like 'test%' vs. substr(a, 1, 4) = 'test'
    original = dc(tree)
    root = tree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, sqlglot.expressions.Like):
                col = value.args['this']
                pattern = value.args['expression'].args['this']
                if '%' in pattern:
                    if pattern.index('%') == len(pattern)-1:
                        new = sqlglot.expressions.EQ()
                        new.args['this'] = sqlglot.expressions.Substring(this=col, start=sqlglot.expressions.Literal(this="1.0", is_string=True), length=sqlglot.expressions.Literal(this=f"{len(pattern)-1}.0", is_string=True))
                        new.args['expression'] = sqlglot.expressions.Literal(this=pattern[:-1], is_string=True)
                        current_node.args[key] = new


    if original != tree:
        print("Applied Rule 16")
    return tree
def rule17(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # order by date vs. order by julianday(date)
    original = dc(tree) 
    if 'order' not in tree.args:
        return tree
    order = tree.args['order']
    if 'expressions' not in order.args:
        return tree
    if len(order.args['expressions']) != 1:
        return tree
    exp = order.args['expressions'][0]
    if 'this' not in exp.args:
        return tree
    val = exp.args['this']
    if isinstance(val, sqlglot.expressions.Anonymous):
        if 'this' in val.args:
            t = val.args['this']
            if t == 'julianday':
                col = val.args['expressions'][0]
            else:
                return tree
        else:
            return tree
    else:
        return tree
    exp.args['this'] = col

    if original != tree:
        print("Applied Rule 17")
    return tree
    
def rule18(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # c in (A, B) -> c = A or c = B, c not in (A, B) -> c != A and c != B 
    original = dc(tree)
    root = tree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, sqlglot.expressions.Not):
                if isinstance(value.args['this'], sqlglot.expressions.In):
                    if 'expressions' in value.args['this'].args:
                        col = value.args['this'].args['this']
                        exprs = value.args['this'].args['expressions']
                        eqs = [sqlglot.expressions.NEQ(this=col,expression = i) for i in exprs]
                        it = iter(eqs)
                        result = next(it)  # Start with the first element
                        
                        for expr in it:
                            result = sqlglot.expressions.And(this=result, expression=expr)
                        current_node.args[key] = result
            if isinstance(value, sqlglot.expressions.In):
                if 'expressions' in value.args:
                    col = value.args['this']
                    exprs = value.args['expressions']

                    eqs = [sqlglot.expressions.EQ(this=col,expression = i) for i in exprs]
                    it = iter(eqs)
                    result = next(it)  # Start with the first element
                    
                    for expr in it:
                        result = sqlglot.expressions.Or(this=result, expression=expr)
                    current_node.args[key] = result
                
                
                
    if tree != original:
        print("Applied Rule 18")
    return tree



def rule19(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # a from t join t2 on a = b vs. b from t join t2 on a = b
    original = dc(tree)
    def replace(t,on):
        if isinstance(on, sqlglot.expressions.And):
            eqs = []  # List to store EQ expressions
            stack = [on]  # Stack to manage traversal

            while stack:
                current = stack.pop()
                if isinstance(current, sqlglot.expressions.EQ):
                    eqs.append(current)  # Add EQ to the result list
                elif isinstance(current, sqlglot.expressions.And):
                    # Push children of AND onto the stack
                    stack.append(current.args['this'])
                    stack.append(current.args['expression'])
        else:
            eqs = [on]
        for eq in eqs:
            # if one of the values is unique, the other is too. if one is non_null, the other is too
            val1 = eq.args['this']
            val2 = eq.args['expression']
            if isinstance(val1, sqlglot.expressions.Column) and isinstance(val2, sqlglot.expressions.Column):
                if 'table' in val1.args and 'table' in val2.args:
                    if 'this' in val1.args['table'].args and 'this' in val2.args['table'].args:
                        col_table_name1 = val1.args['table'].args['this']
                        col_name1 = val1.args['this'].args['this']
                        col_table_name2 = val2.args['table'].args['this']
                        col_name2 = val2.args['this'].args['this']
                        if not isinstance(col_table_name1, sqlglot.expressions.Select) and not isinstance(col_table_name2, sqlglot.expressions.Select):
                            if col_name1 in schema[col_table_name1]['unique']:
                                if col_name2 not in schema[col_table_name2]['unique']:
                                    schema[col_table_name2]['unique'].append(col_name2)
                            if col_name2 in schema[col_table_name2]['unique']:
                                if col_name1 not in schema[col_table_name1]['unique']:
                                    schema[col_table_name1]['unique'].append(col_name1)
                            if col_name1 in schema[col_table_name1]['non_null']:
                                if col_name2 not in schema[col_table_name2]['non_null']:
                                    schema[col_table_name2]['non_null'].append(col_name2)
                            if col_name2 in schema[col_table_name2]['non_null']:
                                if col_name1 not in schema[col_table_name1]['non_null']:
                                    schema[col_table_name1]['non_null'].append(col_name1)
            root = t
            stack = [(root, "")]
            results = []  # To store the traversal paths and leaf values
            while stack:
                current_node, path = stack.pop()
                for key, value in current_node.args.items():
                    current_path = f"{path}/{key}" if path else key
                    if isinstance(value, list):
                        for i in range(len(value)):
                            if isinstance(value[i], sqlglot.expressions.Column):
                                if value[i] == eq.args['expression']:
                                    value[i] = eq.args['this']
                            stack.append((value[i], f"{current_path}[{i}]")) 
                    if isinstance(value, sqlglot.expressions.Select):
                        continue
                    if isinstance(value, Expression):
                        # If the value is an Expression node, add it to the stack
                        stack.append((value, current_path))
                    if isinstance(value, sqlglot.expressions.Column):
                        if current_node in eqs:
                            continue
                        if value == eq.args['expression']:
                            current_node.args[key] = eq.args['this']
        return t
    root = tree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    if isinstance(value[i], sqlglot.expressions.Join):
                        if 'on' in value[i].args and 'side' not in value[i].args:
                            on = value[i].args['on']
                            if isinstance(on, sqlglot.expressions.EQ):
                                # replace everything on 1 side of eq with the other, except here
                                replace(tree,on)
                            elif isinstance(on, sqlglot.expressions.And):
                                replace(tree,on)
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
                
                
                
    if tree != original:
        print("Applied Rule 19")
    return tree

def rule20(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # where cond vs. where t1.c1 in (select c1 from t1 where cond)
    original = dc(tree)
    # for this rule to apply, we must have a where clause using IN on a subquery
    if 'where' not in tree.args:
        return tree
    def process_in(in_clause: sqlglot.expressions.In):
        if 'query' not in in_clause.args: # If it doesn't have a subquery, rule doesn't apply
            return in_clause
        in_col = in_clause.args['this']
        in_sub = in_clause.args['query'].args['this']

        if not isinstance(in_sub, sqlglot.expressions.Select): # If the subquery isn't a select, rule doesn't apply
            return in_clause
        # Now, the in_col must be selected in the subquery, and the from should be the same table as that in_col
        if 'expressions' not in in_sub.args:
            return in_clause
        if len(in_sub.args['expressions']) != 1: # If there are multiple columns selected, rule doesn't apply
            return in_clause
        in_sub_col = in_sub.args['expressions'][0]
        if in_sub_col != in_col: # If the column selected in the subquery isn't the same as the column in the IN clause, rule doesn't apply
            return in_clause
        if 'from' not in in_sub.args:
            return in_clause
        if in_sub.args['from'].args['this'].args['this'] != in_col.args['table']: # If the table in the subquery isn't the same as the table of the column, rule doesn't apply
            return in_clause
        # CONDITIONS ARE MET! Now, we can apply the rule
        # In clause becomes just the subquery's where clause
        if 'where' in in_sub.args:
            return in_sub.args['where'].args['this']
        else: # If there is no where clause, return the original in clause
            return in_clause
    condition = tree.args['where']
    root = condition
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, sqlglot.expressions.Subquery):
                continue
            if isinstance(value, list):
                for i in range(len(value)):
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, sqlglot.expressions.In):
                current_node.args[key] = process_in(value)
    

    if tree != original:
        print("Applied Rule 20")
    return tree
def rule22(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # a between A and B -> a >= A and a <= B
    original = dc(tree)
    root = tree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, sqlglot.expressions.Between):
                # convert to And statement with both LTE and GTE
                col = value.args['this']
                low = value.args['low']
                high = value.args['high']
                newval = sqlglot.expressions.And()
                gte = sqlglot.expressions.GTE()
                lte = sqlglot.expressions.LTE()
                gte.args['this'] = col
                lte.args['this'] = col
                gte.args['expression'] = low
                lte.args['expression'] = high
                newval.args['this'] = gte
                newval.args['expression'] = lte
                current_node.args[key] = newval
                
    if tree != original:
        print("Applied Rule 22")
    return tree

def rule23(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # not != --> =, not <= --> >, etc.
    original = dc(tree)
    root = tree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, sqlglot.expressions.Not):
                # case analysis on what is being Not'd
                match type(value.args['this']): # if it matches these types, we can remove the NOT
                    case sqlglot.expressions.EQ:
                        new = sqlglot.expressions.NEQ()
                        new.args['this'] = value.args['this'].args['this']
                        new.args['expression'] = value.args['this'].args['expression']
                        current_node.args[key] = new
                    case sqlglot.expressions.NEQ:
                        new = sqlglot.expressions.EQ()
                        new.args['this'] = value.args['this'].args['this']
                        new.args['expression'] = value.args['this'].args['expression']
                        current_node.args[key] = new
                    case sqlglot.expressions.GT:
                        new = sqlglot.expressions.LTE()
                        new.args['this'] = value.args['this'].args['this']
                        new.args['expression'] = value.args['this'].args['expression']
                        current_node.args[key] = new
                    case sqlglot.expressions.GTE:
                        new = sqlglot.expressions.LT()
                        new.args['this'] = value.args['this'].args['this']
                        new.args['expression'] = value.args['this'].args['expression']
                        current_node.args[key] = new
                    case sqlglot.expressions.LT:
                        new = sqlglot.expressions.GTE()
                        new.args['this'] = value.args['this'].args['this']
                        new.args['expression'] = value.args['this'].args['expression']
                        current_node.args[key] = new
                    case sqlglot.expressions.LTE:
                        new = sqlglot.expressions.GT()
                        new.args['this'] = value.args['this'].args['this']
                        new.args['expression'] = value.args['this'].args['expression']
                        current_node.args[key] = new
                    case _: # doesn't match, do nothing.
                        pass


    if tree != original:
        print("Applied Rule 23")
    return tree

def rule24(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # iif -> case when
    original = dc(tree)

    root = tree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, sqlglot.expressions.If):
                if 'this' not in value.args:
                    continue
                if 'true' not in value.args:
                    continue
                if 'false' not in value.args:
                    continue
                this = value.args['this']
                true = value.args['true']
                false = value.args['false']
                caseExp = sqlglot.expressions.Case()
                caseExp.args['ifs'] = [sqlglot.expressions.If(this=this, true=true)]
                caseExp.args['default'] = false
                current_node.args[key] = caseExp

    if original != tree:
        print("Applied Rule 24")
    return tree





def rule25(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # a left join b on a.a = b.b where b.anything is null vs. a where a.a not in (select b.b from b)
    original = dc(tree)
    if 'where' not in tree.args:
        return tree
    if 'joins' not in tree.args:
        return tree
    joins = tree.args['joins']
    if not joins:
        return tree
    if len(joins) != 1:
        return tree
    join = joins[0]
    if 'side' not in join.args:
        return tree
    if join.args['side'] != 'left':
        return tree
    where = tree.args['where']
    cond = where.args['this']
    if not isinstance(cond, sqlglot.expressions.Is):
        return tree
    col = cond.args['this']
    expression = cond.args['expression']
    if not isinstance(expression, sqlglot.expressions.Null):
        return tree
    if 'on' not in join.args:
        return tree
    on = join.args['on']
    table = join.args['this']
    if not isinstance(on, sqlglot.expressions.EQ):
        return tree
    if 'this' not in on.args:
        return tree
    if 'expression' not in on.args:
        return tree
    if 'from' not in tree.args:
        return tree
    fromtable = tree.args['from'].args['this']
    v1 = on.args['this']
    v2 = on.args['expression']
    fromtablename = fromtable.args['this'].args['this']
    condtablename = col.args['table'].args['this']
    if v1.args['table'].args['this'] == fromtablename:
        c1 = v1
        if v2.args['table'].args['this'] == condtablename:
            c2 = v2
        else:
            return tree
    else:
        c1 = v2
        if v1.args['table'].args['this'] == condtablename:
            c2 = v1
        else:
            return tree
    # if we get here, we can apply the rule
    subq = sqlglot.expressions.Subquery()
    select = sqlglot.expressions.Select()
    select.args['expressions'] = [c2]
    select.args['from'] = sqlglot.expressions.From(this=sqlglot.expressions.Table(this=sqlglot.expressions.Identifier(this=condtablename, quoted=False)))
    subq.args['this'] = select
    new = sqlglot.expressions.Not()
    new.args['this'] = sqlglot.expressions.In(this=c1, query=subq)
    tree.args['where'] = sqlglot.expressions.Where(this=new)
    tree.args.pop('joins')
    if original != tree:
        print("Applied Rule 25")
    return tree


def cleanTrues(tree: sqlglot.expressions.Select, schema: dict, db: str) -> sqlglot.expressions.Select: # cleans up any 1=1s.
    original = dc(tree)
    root = tree
    def isTrue(ex: Expression) -> bool:
        if isinstance(ex, sqlglot.expressions.EQ):
            if ex.args['this'] == ex.args['expression']:
                return True
        return False
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    results = []  # To store the traversal paths and leaf values
    popwhere = False
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(value, list):
                for i in range(len(value)):
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
            if isinstance(value, sqlglot.expressions.And):
                val1, val2 = value.args['this'], value.args['expression']
                if isTrue(val1):
                    current_node.args[key] = val2
                elif isTrue(val2):
                    current_node.args[key] = val1
            if isinstance(value, sqlglot.expressions.Or):
                val1, val2 = value.args['this'], value.args['expression']
                if isTrue(val1):
                    current_node.args[key] = val2
                elif isTrue(val2):
                    current_node.args[key] = val1
            if isinstance(value, sqlglot.expressions.Where):
                if isTrue(value.args['this']):
                    current_node.args[key] = None
                    popwhere = True
    if popwhere:
        tree.args.pop('where')

            

    if tree != original:
        print("Cleaned Trues")
    return tree


def applyRules(tree: sqlglot.expressions.Select, schema: dict, db: str, rules: list) -> sqlglot.expressions.Select:
    newtree = dc(tree)
    if not tree:
        return
    
    # before processing all subqueries, if the main query has a with clause, process it first
    if 26 in rules:
        if 'with' in newtree.args:
            withExp = newtree.args['with']
            if 'expressions' in withExp.args:
                exps = withExp.args['expressions']
                for exp in exps:
                    if isinstance(exp, sqlglot.expressions.CTE):
                        cte = exp
                        subq = cte.args['this']
                        alias = cte.args['alias']
                        # Now, loop through the main query and replace all instances of the alias with the subquery
                        root = newtree
                        stack = [(root, "")]  # Stack contains tuples of (current_node, path)
                        while stack:
                            current_node, path = stack.pop()
                            for key, value in current_node.args.items():
                                current_path = f"{path}/{key}" if path else key
                                if isinstance(value, list):
                                    for i in range(len(value)):
                                        if isinstance(value[i], sqlglot.expressions.Column):
                                            if 'table' in value[i].args:
                                                if 'this' in value[i].args['table'].args:
                                                    if value[i].args['table'].args['this'] == alias:
                                                        value[i] = subq
                                        stack.append((value[i], f"{current_path}[{i}]")) 
                                if isinstance(value, Expression):
                                    # If the value is an Expression node, add it to the stack
                                    stack.append((value, current_path))
                                if isinstance(value, sqlglot.expressions.Identifier):
                                    if value == alias.args['this'] and current_node != alias:
                                        newq = sqlglot.expressions.Subquery()
                                        newq.args['this'] = subq
                                        current_node.args[key] = newq
            newtree.args.pop('with')
            print("Applied Rule 26")
                            

        
    # process all subqueries
    root = newtree
    stack = [(root, "")]  # Stack contains tuples of (current_node, path)
    while stack:
        current_node, path = stack.pop()
        for key, value in current_node.args.items():
            current_path = f"{path}/{key}" if path else key
            
            if isinstance(value, list):
                for i in range(len(value)):
                    if isinstance(value[i], sqlglot.expressions.Select):
                        print('processing subquery')
                        value[i] = applyRules(value[i], schema, db, rules)
                    current_node.args[key][i] = value[i]
                    stack.append((value[i], f"{current_path}[{i}]")) 
            if isinstance(value, sqlglot.expressions.Select):

                print('processing subquery')
                current_node.args[key] = applyRules(value, schema, db, rules)
            if isinstance(value, Expression):
                # If the value is an Expression node, add it to the stack
                stack.append((value, current_path))
    if 21 in rules:
        if isinstance(newtree, sqlglot.expressions.Intersect) or isinstance(newtree, sqlglot.expressions.Union):
            if(newtree.args['this']==newtree.args['expression']):
                print("Applied Rule 21")
                newtree = dc(newtree.args['this'])
    if 3 in rules:
        if isinstance(newtree, sqlglot.expressions.Intersect): # c1 from t where a intersect c1 from t where b vs. c1 from t where a and b: only if c1 is unique
            original = dc(newtree)
            sub1 = newtree.args['this']
            sub2 = newtree.args['expression']
            if 'expressions' in sub1.args and 'expressions' in sub2.args:
                if len(sub1.args['expressions']) == 1 and len(sub2.args['expressions']) == 1:
                    if sub1.args['expressions'] == sub2.args['expressions']:
                        if isinstance(sub1.args['expressions'][0], sqlglot.expressions.Column):
                            if 'table' in sub1.args['expressions'][0].args:
                                col_table_name = sub1.args['expressions'][0].args['table'].args['this']
                                if not isinstance(sub1.args['expressions'][0].args['this'], sqlglot.expressions.Star):
                                    col_name = sub1.args['expressions'][0].args['this'].args['this']
                                    if col_name in schema[col_table_name]['unique']:
                                        if sub1.args['from'] == sub2.args['from']:
                                            if 'where' in sub1.args and 'where' in sub2.args:
                                                newwhere = sqlglot.expressions.And(this=sub1.args['where'].args['this'], expression=sub2.args['where'].args['this'])
                                                sub1.args['where'].args['this'] = newwhere
                                                newtree = dc(sub1)

            if newtree != original:
                print("Applied Rule 3")
        
        if isinstance(newtree, sqlglot.expressions.Union): # c1 from t where a union c1 from t where b vs. c1 from t where a or b: only if c1 is unique
            original = dc(newtree)
            sub1 = newtree.args['this']
            sub2 = newtree.args['expression']
            if 'expressions' in sub1.args and 'expressions' in sub2.args:
                if len(sub1.args['expressions']) == 1 and len(sub2.args['expressions']) == 1:
                    if sub1.args['expressions'] == sub2.args['expressions']:
                        if isinstance(sub1.args['expressions'][0], sqlglot.expressions.Column):
                            if 'table' in sub1.args['expressions'][0].args:
                                col_table_name = sub1.args['expressions'][0].args['table'].args['this']
                                if not isinstance(sub1.args['expressions'][0].args['this'], sqlglot.expressions.Star):
                                    col_name = sub1.args['expressions'][0].args['this'].args['this']
                                    if col_name in schema[col_table_name]['unique']:
                                        if sub1.args['from'] == sub2.args['from']:
                                            if 'where' in sub1.args and 'where' in sub2.args:
                                                newwhere = sqlglot.expressions.Or(this=sub1.args['where'].args['this'], expression=sub2.args['where'].args['this'])
                                                sub1.args['where'] = newwhere
                                                newtree = dc(sub1)

            if newtree != original:
                print("Applied Rule 3")
    
    if 5 in rules:
        if isinstance(newtree, sqlglot.expressions.Except): # c1 from t except (q1) vs. c1 from t where c1 not in (q1): only if c1 is unique and non_null
            original = dc(newtree)
            outer = newtree.args['this']
            inner = newtree.args['expression']
            if 'expressions' in outer.args:
                if len(outer.args['expressions']) == 1:
                    column = outer.args['expressions'][0]
                    if isinstance(column, sqlglot.expressions.Column):
                        if 'table' in column.args:
                            col_table_name = column.args['table'].args['this']
                            if not isinstance(column.args['this'], sqlglot.expressions.Star):
                                col_name = column.args['this'].args['this']
                                if col_name in schema[col_table_name]['unique'] and col_name in schema[col_table_name]['non_null']:
                                    # conditions are met for rule 6
                                    t = dc(outer)
                                    if 'where' in t.args:
                                        
                                        t.args['where'] = sqlglot.expressions.Where(this=sqlglot.expressions.And(this=sqlglot.expressions.Not(this=sqlglot.expressions.In(this=column, query=sqlglot.expressions.Subquery(this=inner))), expression=t.args['where'].args['this']))
                                    else:
                                        t.args['where'] = sqlglot.expressions.Where(this=sqlglot.expressions.Not(this=sqlglot.expressions.In(this=column, query=sqlglot.expressions.Subquery(this=inner))))
                                    newtree = dc(t)

            if newtree != original:
                print("Applied Rule 5")
    if isinstance(newtree, sqlglot.expressions.Select):
        oldtree = None
        while newtree != oldtree:
            oldtree = dc(newtree)
            if 100 in rules:
                newtree = rule100(newtree, schema, db)
            if 101 in rules:
                newtree = rule101(newtree, schema, db)
            if 102 in rules:
                newtree = rule102(newtree, schema, db)
            if 103 in rules:
                newtree = rule103(newtree, schema, db)
            if 104 in rules:
                newtree = rule104(newtree, schema, db)
            if 105 in rules:
                newtree = rule105(newtree, schema, db)
            if 106 in rules:
                newtree = rule106(newtree, schema, db)
            if 107 in rules:
                newtree = rule107(newtree, schema, db)  
            if 108 in rules:
                newtree = rule108(newtree, schema, db)
            if 1 in rules:
                newtree = rule1(newtree, schema, db)
            if 2 in rules:
                newtree = rule2(newtree, schema, db)
            if 4 in rules:
                newtree = rule4(newtree, schema, db)
            if 6 in rules:
                newtree = rule6(newtree, schema, db)
            if 7 in rules:
                newtree = rule7(newtree, schema, db)
            if 8 in rules:
                newtree = rule8(newtree, schema, db)
            if 9 in rules:
                newtree = rule9(newtree, schema, db)
            if 10 in rules:
                newtree = rule10(newtree, schema, db)
            if 11 in rules:
                newtree = rule11(newtree, schema, db)
            if 12 in rules:
                newtree = rule12(newtree, schema, db)
            if 13 in rules:
                newtree = rule13(newtree, schema, db)
            if 14 in rules:
                newtree = rule14(newtree, schema, db)
            if 15 in rules:
                newtree = rule15(newtree, schema, db)
            if 16 in rules:
                newtree = rule16(newtree, schema, db)
            if 17 in rules:
                newtree = rule17(newtree, schema, db)
            if 18 in rules:
                newtree = rule18(newtree, schema, db)
            if 19 in rules:
                newtree = rule19(newtree, schema, db)
            if 20 in rules:
                newtree = rule20(newtree, schema, db)
            if 22 in rules:
                newtree = rule22(newtree, schema, db)
            if 23 in rules:
                newtree = rule23(newtree, schema, db)
            if 24 in rules:
                newtree = rule24(newtree, schema, db)
            if 25 in rules:
                newtree = rule25(newtree, schema, db)
            
            newtree = cleanTrues(newtree, schema, db)
        
    return newtree

def compareTrees(tree1: sqlglot.expressions.Select, tree2: sqlglot.expressions.Select, schema: dict, db: str, rules: list) -> bool:

    
    print('tree1rules')
    tree1 = applyRules(tree1,schema, db, rules)
    print()
    print('tree2rules')
    tree2 = applyRules(tree2,schema, db, rules)



    print()

    # print(repr(tree1))
    # print(repr(tree2))
    print("Pred after applying rules:",tree1)
    print("Gold after applying rules:",tree2)
    return tree1 == tree2

if __name__ == "__main__":

    ALLRULES = [100,101,102,103,104,105,106,107,108,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26]
    data = []
    parser = argparse.ArgumentParser()
    parser.add_argument('--pred', type=str, default='', help='file containing the predictions')
    parser.add_argument('--gold', type=str, default='', help='file containing the gold data')
    parser.add_argument('--db', type=str, default='', help='folder containing the database files')
    parser.add_argument('--table', type=str, default='', help='the tables json file')
    parser.add_argument('--etype', type=str, default='all',help='exe, treematch, or all')
    parser.add_argument('--verbose', default=False,action='store_true', help='Whether to print verbose output')
    args = parser.parse_args()

    predfile = args.pred
    goldfile = args.gold
    tablefile = args.table
    with open(predfile, 'r') as f:
        preds = f.readlines()
    with open(goldfile, 'r') as f:
        golds = f.readlines()
    # if preds doesn't have same length as golds, insert empty lines in the same locations as golds
    if preds[-1] == "\n":
        preds = preds[:-1]
    if len(preds) != len(golds):
        for i in range(len(golds)):
            if golds[i] == "\n":
                preds.insert(i, "\n")

    # sort into list of lists, each list is split by the empty string in the previous
    c = 0
    data_preds = []
    data_golds = []
    for i in range(len(preds)):
        if preds[i] == "\n":
            data_preds.append(preds[c:i])
            data_golds.append(golds[c:i])
            c = i+1
    if c < len(preds):
        data_preds.append(preds[c:])
        data_golds.append(golds[c:])
    # tqdm
    schemas = {}
    total = 0
    count_exec = 0
    count_treematch = 0

    for i in tqdm.tqdm(range(len(data_preds))):
        if args.verbose:
            print('Conversation: ',i)
        for j in range(len(data_preds[i])):
            if args.verbose:
                print("Utterance: ",j)
            gold, db = data_golds[i][j].split('\t')[0].strip(), data_golds[i][j].split('\t')[1].strip()
            db = f"{args.db}{db}/{db}.sqlite"
            pred = data_preds[i][j].strip()

        
            if db not in schemas:
                schema = get_schema(db)
                schemas[db] = schema
            gold = preprocess(gold, schema)
            pred = preprocess(pred, schema)
            if args.verbose:
                print("gold: ",gold)
                print("pred: ",pred)
                print("DB: ",db)
            # is query bad?
            # gold = "select * from model_list"
            # pred = "select * from model_list"
            # db = "ESMp/cosql_dev/database/car_1/car_1.sqlite"
            conn = sqlite3.connect(db)
            c = conn.cursor()
            bad = False
            try:
                c.execute("EXPLAIN QUERY PLAN " + gold)
                
                c.execute("EXPLAIN QUERY PLAN " + pred)
            except:
                bad = True
            rules = ALLRULES
            if not bad:
                if args.verbose:
                    treegold = parseTree(gold)
                else:
                    with contextlib.redirect_stdout(open(os.devnull, 'w')):
                        treegold = parseTree(gold)
                try:
                    if args.verbose:
                        treepred = parseTree(pred)
                    else:
                        with contextlib.redirect_stdout(open(os.devnull, 'w')):
                            treepred = parseTree(pred)
                except:
                    treepred = None
                try:
                    if args.verbose:
                        treecomp = compareTrees(treegold,treepred,dc(schemas[db]), db, rules)
                    else:
                        with contextlib.redirect_stdout(open(os.devnull, 'w')):
                            treecomp = compareTrees(treegold,treepred,dc(schemas[db]), db, rules)
                except:
                    treecomp = False
            else:
                treecomp = False
            execcomp = evalquery(gold,pred,db,'exec',False,True,False,False,False,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20],False)
            if treecomp:
                count_treematch += 1
            if execcomp:
                count_exec += 1
            total += 1
    print("RESULTS")
    print("Total: ",total)
    if args.etype == 'all' or args.etype == 'treematch':
        print("ETM: ", count_treematch/total)
    if args.etype == 'all' or args.etype == 'exe':
        print("EXE: ", count_exec/total)