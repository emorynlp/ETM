# ETM: A New Evaluation Metric for Text-To-SQL

ETM is a new metric for the Text-to-SQL task. ETM calculates semantic accuracy with a lower rate of false positives than Execution accuracy and a lower rate of false negatives than Exact Set Matching. It is released along with several other state of the art model outputs. This repo contains all the code necessary for evaluation.

### Evaluation
`treeMath.py` is written in Python 3.12.
To run this evaluation you need gold and predicted txt files. Examples of these are linked in [spider_dev](spider_dev/), [spider_test](spider_test/), [cosql_dev](cosql_dev/), and [bird_dev](bird_dev/). In each of these folders,
- `gold.txt`: gold file where each line is `gold SQL \t db_id`
- `C3.txt`: [C3 model](https://github.com/bigbigwatermalon/C3SQL) predictions
- `DAIL.txt`: [DAIL model](https://github.com/BeachWang/DAIL-SQL) predictions
- `DIN.txt`: [DIN model](https://github.com/MohammadrezaPourreza/Few-shot-NL2SQL-with-prompting) predictions
- `RASAT+PICARD.txt`: [RASAT+PICARD](https://github.com/LUMIA-Group/rasat) predictions
- `RESDSQL.txt`: [RESDSQL](https://github.com/RUCKBReasoning/RESDSQL) predictions
- `SuperSQL.txt`: [SuperSQL](https://github.com/BugMaker-Boyan/NL2SQL360) predictions
- `codeS.txt`: [CodeS-7b](https://github.com/RUCKBReasoning/codes) predictions

### Install & Run

First, download the database folders for [spider](https://drive.usercontent.google.com/download?id=1iRDVHLr4mX2wQKSgA9J8Pire73Jahh0m&export=download&authuser=0) (dev and test), [cosql](https://drive.usercontent.google.com/download?id=1Y3ydpFiQQ3FC0bzdfy3groV95O_f1nXF&export=download&authuser=0) (only dev), and/or [bird](https://bird-bench.oss-cn-beijing.aliyuncs.com/dev.zip) (dev).
Save the database folders in their respective database folder ([spider_dev/database](spider_dev/database/), [spider_test/database](spider_test/database/), [cosql_dev/database](cosql_dev/database/), [bird_dev/database](bird_dev/database/))

Then, create a conda environment:

```conda create -n "ETM" python=3.12.3```

```conda activate ETM```

Install packages:

```pip install -r requirements.txt```

To run our script, use the following command:

```python3 treeMatch.py --gold path/to/gold.txt --pred path/to/pred.txt --db path/to/database/folder/ --table path/to/tables.json```

##### Required flags:

```--gold```: gold txt file.

```--pred```: predictions txt file.

```--db```: directory of databases.

```--table```: tables json file.

##### Optional flags:
```--etype```: Evaluation type (exe, treematch, or all). Default is all.

```--verbose```: add if you want information like which rules are being applied on each comparison.
