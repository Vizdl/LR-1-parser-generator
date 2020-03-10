package cn.vizdl.LR1.version3;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Scanner;
import java.util.Set;

/*
项目名 :  LR(1) parser generator (LR(1)语法分析器生成器)
项目分析 : 
	输入 : 输入某文件内存地址。且内部采用  <Expr> ::=  <Term> + <Factor>; 的结构输入的LR(1)语法。
	这里的仅支持 BNF范式内部的 终结符,非终结符,或运算,;(表示产生式结束),::=(表示为定义为)
	在这里不支持闭包,也就是{},因为闭包可以转换为非终结符的递归。
		输入文本格式 : 要求输入语法为 无回溯语法,在前瞻一个符号的情况下,总能预测正确的产生式规则。
			start : <aim_name>  //aim_name表示起始符号名称 
		例子 : 
		//这是错误的例子,不符合LR(1)语法
			start : <Goal>;
			<Goal> ::= <Expr>;
			<Expr> ::= <Expr> "+" <Term> | <Expr> "-" <Term>;
			<Term> ::= <Term> "*" <Factor> | <Term> "/" <Factor>;
			<Factor> ::= "number";
			#
			
			
			start : <Goal>;
			<Goal> ::= <Expr>;
			<Expr> ::= <Term><Expr'>;
			<Expr'> ::= "+" <Term><Expr'> 
					|	"-" <Term><Expr'> 
					|	"ε";
			<Term> ::= <Factor><Term'>;
			<Term'> ::= "*" <Factor><Term'>
					|	"/" <Factor><Term'>
					|	"ε";
			<Factor> ::= "("<Expr>")"
					|	"num"
					|	"name";
			#
			
			
			start : <Goal>;
			<Goal> ::= <List>;
			<List> ::= <List><Pair>
					|	<Pair>;
			<Pair> ::= "(" <Pair> ")"
					|	"("")";
			#
		以#作为结尾
	输入分析 : 因为上下文无关语法是一个四元组,而LR(1)语法又是上下文无关语法的子集。所以采用四元组的形式来表示LR(1)语法,是不会损失信息的。
		四元组 (T,NT,S,P)
		T ： 终结符集合
		NT : 非终结符集合
		S : 语法的起始符号(非终结符)
		P : 产生式集合 
		T, NT都可以用一个hash_set来表示。
		P 可以分为两个部分,左侧一定是一个非终结符,右侧是一个支持或运算的产生式。 
		产生式左端可以使用Node节点来表示,产生式右端可以使用多个链表(具体有几个取决于当前产生式有多少个或运算符)来表示。
		将当下语法分为三级,第一级是Expr,第二级别是Term,第三个级别是Factor
		<Expr> ::= <Term> { "|" <Term>}; //产生式(表达式)可以表达成多个小句子 或 起来
		<Term> ::= <Factor> { "+" <Factor>}; // + 表示连接
		<Factor> ::= <T> | <NT>
	输出 : Action 和 GoTo 表。 
	
	1.0完成进度 : 完成了将 输入字符串 转换成了 中间数据结构(BnfContainer)表示。
	2.0完成进度 : closure()闭包函数
	在这里 [A -> β·Cθ,a]指的是,识别完了A后非终结符号为a(也就是LR(1)中的1,前瞻一个符号)。
	关于FIRST : 
		FIRST(A) : 对于语法符号A,FIRST(A)表示,从A推导出的符号串的第一个单词所对应的终结符的集合。
		FIRST定义域 : T ∪ NT ∪ {ε, eof}
		FIRST值域 : T ∪ {ε, eof}
		如若A等于T ∪ {ε, eof}
		那么 FIRST(A) = A
	在闭包函数中,难点在于 FIRST(θa),这不是一个简单的 FIRST(θ),因为多了一个非终结符号 a。
	这是为了防止FIRST(θ)为ε的情况,这样FIRST(θa)退化为FIRST(a) = {a}
	closure(s) : 
	while (s is still changing)
		for each item [A -> β·Cθ,a] ∈ s		//从当前s集中寻求新状态
			for each production C -> γ ∈ P  //有效产生式
				for each b ∈ FIRST(θa)		//如若是可能是前瞻符号(非终结符)
					s <- s ∪ {[C -> ·γ,b]}
					
	//这里x是语法符号,可以是终结符,也可以是非终结符
	goto(s, x)
	moved <- ∅
	for each item ∈ s		//对于s集中的每个项
		if the from of i is [A -> β·xθ,a] then
			moved <- moved ∪ {[A -> βx·θ,a]}
	return closure (moved)
	
	构建CC的算法:
	CC0 <- closure({[S' -> ·S,eof]}) //构建初始状态集
	CC <- {CC0}		//将初始状态集添加到规范族CC中
	while (new set are still being added to CC)		
		for each unmarked set CCi ∈ CC	//unmarked : 未标记的
			mark CCi as processed	//将CCi标记为处理过的
			for each x following a · in an item in CCi  //对于CCi中项a ·后面的每个x
				temp <- goto(CCi, x)
				if temp ∉ CC
					then CC <- CC ∪ {temp}
				record transition from CCi to temp on x
	例子 : 
	<Goal> ::= <List>;
	<List> ::= <List> <Pair> | <Pair>;
	<Pair> ::= "(" <Pair> ")" | "(" ")";
	closure({[Goal -> ·List,eof]})
	
	理解 : 将整个BNF范式语句全都替换成非终结符,结果可能会有很多个。
	但是这可以组成一个DFA,但是许多项都表示的其实是同一种状态,所以需要
	closure来将这些状态来并到同一个集合内,而goto则是从某个状态集接各种符号
	,转移到一个新的状态集,这里即可以是终结符,也可以是非终结符。但是转移后不一定
	能包含所有的这一状态下的项,所以仍需要闭包运算来完善状态集。
	
	如何表示一个项？
	一个项包含三个元素,第一是产生式,第二是 · ,第三是前瞻符号。
	这可以用三个数字来表示。可以使用一个NODE来表示,
	但是这样好像就用不了set,来筛选是否重合了。
	字符串表示法？
	使用字符串,并且两个中隔符号隔开三个数据。
	如若需要,再从字符串转换为数字。
	
	3.0版本完成进度 :
	填表算法 : 
	Action表  纵轴是状态,横轴是 前瞻符号(终结符),内容是规约,状态转移,接收以及失败。
	Goto表  纵轴是状态,横轴是 前瞻符号(非终结符),当进行规约操作后,可以依靠栈中之前的状态,
	加上前瞻的非终结符,来进行状态转移。
	
	for each CCi ∈ CC
		for each  item I ∈ CCi
			if I is [A -> β·cθ,a] and goto (CCi , c) = CCj then
				Action[i,c] <- "shift j"
			else if I is [A -> β·,a] then	//规约
				Action[i,a] <- "reduce A->B"
			else if I is [S'->S·,eof] then	//如若是目标项产生式推导完成状态并且前瞻符号为eof,则为接收状态。
				Action[i,eof] <- "accept"
		for each n ∈ NT				//如若项集CCi跳过一个非终结符n即到达j
			if goto(CCi, n) = CCj then
				Goto[i,n] <- j
				
	如何表示几种状态?
	可以使用位来保证两种状态不混合, shift j直接填入j,而reduce A -> B则或上整型最高位。
这个图的状态 对应 书上状态
0 - 0
1 - 1
6 - 6
这里r是产生式下标...,而不是表达式下标...。
因为我们采用的结构是产生式 -> 表达式,也就是一个产生式连接多个表达式。

本图 对应 书上图(状态)
0 - 0
1 - 1
6 - 6
4 - 4
11 - 11
9 - 9
2 - 3
3 - 2
5 - 7
7 - 5
10 - 8
8 - 10
Action表如下
	eof	(	)	
0	err	s2	err	
1	acc	s2	err	
2	err	s6	s5	
3	r3	r3	err	
4	r2	r2	err	
5	r5	r5	err	
6	err	s6	s8	
7	err	err	s10	
8	err	err	r5	
9	err	err	s11	
10	r4	r4	err	
11	err	err	r4	
Goto表如下
	Goal	List	Pair	
0	err	s1	s3	
1	err	err	s4	
2	err	err	s7	
3	err	err	err	
4	err	err	err	
5	err	err	err	
6	err	err	s9	
7	err	err	err	
8	err	err	err	
9	err	err	err	
10	err	err	err	
11	err	err	err	


*/ 
public class Demo2 {
	public static void main (String[] args) {
		//将输入的产生式都放入ch中
		Scanner scanner = new Scanner(System.in);
		String s = new String();
		String c;
		//输入处理...
		while (true) {
			c = scanner.nextLine();
			int i;
			for (i = 0; i < c.length(); i++) {
				if (c.charAt(i) != '#')
					s += c.charAt(i);
				else {
					scanner.close();
					break;
				}
			}
			if (i != c.length()) {
				break;
			}
		}
		BnfContainer bc = new BnfContainer();
		CodeAnalyzer ca = new CodeAnalyzer(s, bc);
		ca.analyze();
		bc.toLRTable();
		bc.printBNF();
		bc.printActionAndGotoTable();
	}
}

/**
 * 用来装载BNF范式的信息。
 */
class BnfContainer {
	/**
	 * 内部类,NT的节点。
	 * @author HP
	 */
	class NTNode {
		private String name; //符号id
		private List<List<Integer>> expr;
		public NTNode(String name) {
			expr = new ArrayList<List<Integer>>();
			this.name = name;
		}
		/**
		 * 添加一条expr
		 * 返回这个expr的下标
		 * @return
		 */
		public int addExpr() {
			expr.add(new ArrayList<Integer>());
			return expr.size() - 1;
		}
		/**
		 * 向下标为idx的expr添加value
		 * @param idx
		 * @param value
		 */
		public void addExprElement (int idx, int value) {
			this.expr.get(idx).add(value);
		}
		/**
		 * 向最后一个表达式添加value
		 * @param value
		 */
		public void addExprElement (int value) {
			this.addExprElement(this.expr.size() - 1, value);
		}
		
		public void printNTNode () {
			System.out.println("NTNumber : " + this.name);
			for (List<Integer> list : this.expr) {
				for (Integer val : list) {
					System.out.print(val + " ");
				}System.out.println();
			}
		}
	}
	
	
	//常量定义
	/**
	 * 这两个常量只出现在终结符
	 * 因为要将终结符和非终结符
	 * 放在同一个链表中
	 * 所以使用这个来辨别终结符和非终结符。
	 */
	private static final int MASK = 0X80000000; //掩码,用来给终结符做掩饰的编码。
	private static final int DECODE = 0X7fffffff; //解码,破译掩码得到原本的编码。
	private static final String separationCharacter = " ";
	/**
	 * 非终结符Map 
	 * key : 非终结符名称
	 * value : 非终结符在production链表中的下标
	 */
	private HashMap<String,Integer> NTMap;
	/**
	 * 终结符Map 
	 * key : 终结符名称
	 * value : 终结符在T链表中的下标
	 */
	private HashMap<String,Integer> TMap;
	// 终结符链表
	private ArrayList<String> T;
	// 产生式链表,因为一个非终结符一个产生式具有双射关系。
	private ArrayList<NTNode> production;
	//如若未设置,默认为0
	public int startIndex = 0;
	private int eof, epsilon;
	/**
	 * 这个数组包含了所有非终结符的FIRST
	 */
	private Set<Integer>[] First;
	/**
	 * 要输出的Action表
	 */
	private int[][] Action;
	/**
	 * 要输出的Goto表
	 */
	private int[][] Goto;
	
	public BnfContainer() {
		//内部数据结构初始化
		NTMap = new HashMap<String,Integer>();
		TMap = new HashMap<String,Integer>();
		T = new ArrayList<String>();
		production = new ArrayList<NTNode>();
		
		
		//添加两个特殊的非终结符 eof 和 ε
		this.addT("eof");
		this.addT("ε");
		eof = this.getTSerialNumber("eof");
		epsilon = this.getTSerialNumber("ε");
	}
	
	/**
	 * 设置开始非终结符
	 * @param name
	 */
	public void setStart (String name) {
		this.addNT(name);
		this.startIndex = this.NTMap.get(name);
	}
	
	/**
	 * 将非终结符的名字传入,即可添加一个非终结符节点。
	 * @param name
	 */
	public void addNT (String name) {
		if (name.isEmpty()) {
			System.out.println("终结符不可为空");
			System.exit(-1);
		}
		if (!NTMap.containsKey(name)) {
			NTNode node = new NTNode(name);
			NTMap.put(name, production.size());
			production.add(node);
		}
	}
	
	/**
	 * 将终结符传入,增加非终结符。
	 * @param name
	 */
	public void addT(String name) {
		if (!this.TMap.containsKey(name)) {
			this.TMap.put(name, T.size());
			this.T.add(name);
		}
	}
	
	/**
	 * 输入终结符名称
	 * 获取终结符编号
	 * 如若存在当前终结符,返回编号
	 * 否则返回-1,输出错误警告并且退出。
	 * @param name
	 * @return
	 */
	private int getTSerialNumber (String name) {
		this.notFindTWarning(name);
		return this.TMap.get(name) | BnfContainer.MASK;
	}
	
	/**
	 * 输入非终结符名称
	 * 获取非终结符编号
	 * 如若存在当前非终结符,返回编号
	 * 否则返回-1,输出错误警告并且退出。
	 * @param name
	 * @return
	 */
	private int getNTSerialNumber (String name) {
		this.notFindNTWarning(name);
		return this.NTMap.get(name);
	}
	
	/**
	 * 创建新的表达式并添加到名称为name的非终结符节点上
	 * 返回表达式编号
	 */
	public int creatNewExper(String name) {
		this.notFindNTWarning(name);
		NTNode ntn = this.production.get(this.NTMap.get(name));
		return ntn.addExpr();
	}
	/**
	 * 向左端非终结符名称为name的产生式
	 * 第idx表达式添加元素
	 * @param name
	 * @param idx
	 * @param isNt
	 */
	public void addExpeElement(String name, int idx,boolean isNt, String addElement) {
		NTNode ntn = this.production.get(this.NTMap.get(name));
		if (isNt) {
			this.notFindNTWarning(name);
			this.notFindNTWarning(addElement);
			ntn.addExprElement(idx, this.getNTSerialNumber(addElement));
		}else {
			this.addT(addElement);
			ntn.addExprElement(idx, this.getTSerialNumber(addElement));
		}
	}
	
	/**
	 * 向左端非终结符名称为name的产生式
	 * 最后一个表达式添加元素
	 * @param name
	 * @param list
	 */
	public void addExpeElement(String name,boolean isNt, String addElement) {
		NTNode ntn = this.production.get(this.NTMap.get(name));
		if (isNt) {
			this.notFindNTWarning(name);
			this.notFindNTWarning(addElement);
			ntn.addExprElement(this.getNTSerialNumber(addElement));
		}else {
			this.addT(addElement);
			ntn.addExprElement(this.getTSerialNumber(addElement));
		}
	}
	
	/**
	 * 如若找到了当前非终结符,什么都不会发生。
	 * 否则会提示并且退出程序
	 * @param name
	 */
	private void notFindNTWarning(String name) {
		if (!this.NTMap.containsKey(name)) {
			System.out.println("错误的非终结符" + name + "!");
			System.exit(-1);
		}
	}
	/**
	 * 如若找到了当前终结符,什么都不会发生。
	 * 否则会提示并且退出程序
	 * @param name
	 */
	private void notFindTWarning(String name) {
		if (!this.TMap.containsKey(name)) {
			System.out.println("错误的终结符" + name + "!");
			System.exit(-1);
		}
	}

	public void printBNF() {
		System.out.println("开始非终结符为 : " + this.production.get(startIndex).name);
		System.out.println("终结符对应表 : ");
		for (int i = 0; i < this.T.size(); i++) {
			System.out.println(this.T.get(i) + " : " + (i | MASK));
		}
		System.out.println("非终结符对应表 : ");
		for (int i = 0; i < this.production.size(); i++) {
			System.out.println(this.production.get(i).name + " : " + i);
		}
		for (NTNode ntn : this.production) {
			ntn.printNTNode();
		}
		
		System.out.println("First集 : ");
		int count = 0;
		for (Set<Integer> s : First) {
			System.out.println("第" + count + "个非终结符" + this.production.get(count).name);
			for (Integer i : s) {
				this.printSymbol(i);
			}System.out.println();
			count++;
		}
		System.out.println("一共有 " + this.CC.size() + " 种状态");
		for (Set<String> s : this.CC) {
			this.printCCSet(s);
		}
	}
	/**
	 * 输出项集 s
	 * @param s
	 */
	private void printCCSet(Set<String> s) {
		for (String item : s) {
			this.printItem(item);
		}
		System.out.println();
	}
	
	
	private void printItem (String item) {
		String[] strs = item.split(BnfContainer.separationCharacter); // ! 为分隔符
		int productionIdx = Integer.parseInt(strs[0]); //产生式下标
		int exprIdx = Integer.parseInt(strs[1]); //表达式下标
		int placeholder = Integer.parseInt(strs[2]); //占位符下标 这个下标从0开始(表示左侧无语法符号)。
		int prospectiveSymbol = Integer.parseInt(strs[3]);//前瞻符
		NTNode ntn = this.production.get(productionIdx);
		System.out.print("[" + ntn.name + "::=");
		List<Integer> list = ntn.expr.get(exprIdx);
		for (int i = 0; i < list.size(); i++) {
			if (i == placeholder) {
				System.out.print("·");
			}
			this.printSymbol(list.get(i));
			System.out.print(" ");
		}
		if (list.size() == placeholder) {
			System.out.print("·");
		}
		System.out.print(",");
		this.printSymbol(prospectiveSymbol);
		System.out.print("]\t");
	}
	
	private void printSymbol (int sym) {
		if (this.isT(sym)) {
			System.out.print(this.T.get(sym & DECODE));
		}else {
			System.out.print(this.production.get(sym).name);
		}
	}
	
	/**
	 * 求所有非终结符符号的FIRST集(终结符的FIRST就是它本身)
	 * FIRST(A) : 对于语法符号A,FIRST(A)表示,
	 * 从A推导出的符号串的第一个单词所对应的终结符的集合。
	 */
	private void FIRSTAllSymbol() {
		First = new HashSet[this.production.size()];
		for (int i = First.length - 1; i >= 0; i--) {
			FIRST(i);
		}return;
	}
	/**
	 * 输入非终结符下标
	 */
	private void FIRST(int idx) {
		if (First[idx] != null) {
			return;
		}First[idx] = new HashSet<Integer>();
		List<List<Integer>> next = this.production.get(idx).expr;
		for (List<Integer> list : next) {
			int val = list.get(0);
			//非终结符
			if (this.isT(val)) {
				First[idx].add(val);
			}else {
				this.FIRST(val);
				First[idx].addAll(First[val]);
			}
		}
	}
	
	private boolean isT (int val) {
		return (val & MASK) == MASK;
	}
	/**
	 * 一个产生式项
	 * 分别有四个元素
	 * productionIdx : 产生式下标
	 * exprIdx : 表达式下标
	 * placeholder : 占位符
	 * prospectiveSymbol : 前瞻符
	 */
	/**
	闭包运算
	closure(s) : 
	while (s is still changing)
		for each item [A -> β·Cθ,a] ∈ s		//从当前s集中寻求新状态
			for each production C -> γ ∈ P  //有效产生式
				for each b ∈ FIRST(θa)		//如若是可能是前瞻符号(非终结符)
					s <- s ∪ {[C -> ·γ,b]}
	 */
	private List<Set<String>> CC;
	private void closure (Set<String> s) {
		int lastSize = -1;
		while (lastSize != s.size()) {
			lastSize = s.size();
			Set<String> hashset = new HashSet<String>();
			for (String item : s) {
				String[] strs = item.split(BnfContainer.separationCharacter); //  为分隔符
				int productionIdx = Integer.parseInt(strs[0]); //产生式下标
				int exprIdx = Integer.parseInt(strs[1]); //表达式下标
				int placeholder = Integer.parseInt(strs[2]); //占位符下标 这个下标从0开始(表示左侧无语法符号)。
				int prospectiveSymbol = Integer.parseInt(strs[3]);//前瞻符
				List<Integer> temp = this.production.get(productionIdx).expr.get(exprIdx);
				//for each item [A -> β·Cθ,a] ∈ s		//从当前s集中寻求新状态
				//	for each production C -> γ ∈ P  //有效产生式
				//temp.get(placeholder) 为 这里的 C
				//条件为 C不是终结符 且 当前占位符未达到最右端    如若C是个终结符,那么就无法拓展,如若占位符已经到达最右端,也无法拓展。
				if (placeholder < temp.size() && !this.isT(temp.get(placeholder))) {
					int cIdx = temp.get(placeholder);
					//先求FIRST(占位符后的串)
					Set<Integer> set = this.FIRSTNextStr(temp, placeholder + 1, prospectiveSymbol);
					List<List<Integer>> expr = this.production.get(cIdx).expr;
					for (int i = 0; i < expr.size(); i++){
						for (Integer val : set) {
							String res = cIdx + BnfContainer.separationCharacter + i + BnfContainer.separationCharacter + 0 + BnfContainer.separationCharacter + val;
							hashset.add(res);
						}
					}
				}
			}s.addAll(hashset);
		}
		/**
		 * 项集之间会有交集,
		 * start : <Goal>;
		 * <Goal> ::= <List>;
		 * <List> ::= <List><Pair>
		 * 		|	<Pair>;
		 * <Pair> ::= "(" <Pair> ")"
		 * 		|	"("")";
		 * #
		 * 书上这个例子的原项 CC0 和 CC1就重复了 [Pair ::= ·(Pair),(]
		 * 当然还有其他的也重复了...
		 */
		return;
	}
	/*
	goto(s, x)
	moved <- ∅
	for each item ∈ s		//对于s集中的每个项
		if the from of i is [A -> β·xθ,a] then
			moved <- moved ∪ {[A -> βx·θ,a]}
	return closure (moved)
	*/
	private Set<String> go (Set<String> s, int x){
		Set<String> res = new HashSet<String>();
		for (String item : s) {
			String[] strs = item.split(BnfContainer.separationCharacter); // ! 为分隔符
			int productionIdx = Integer.parseInt(strs[0]); //产生式下标
			int exprIdx = Integer.parseInt(strs[1]); //表达式下标
			int placeholder = Integer.parseInt(strs[2]); //占位符下标 这个下标从0开始(表示左侧无语法符号)。
			int prospectiveSymbol = Integer.parseInt(strs[3]);//前瞻符
			List<Integer> temp = this.production.get(productionIdx).expr.get(exprIdx);
			String str = new String();
			if (placeholder + 1 <= temp.size() && temp.get(placeholder) == x) {
				str = productionIdx + BnfContainer.separationCharacter + exprIdx + BnfContainer.separationCharacter + (placeholder + 1) + BnfContainer.separationCharacter + prospectiveSymbol;
				res.add(str);
			}
		}
		this.closure(res);
		return res;
	}
	
	/**
	 * 获取    从expr表达式中下标为idx的语法符号开始的串     的FIRST
	 * @param expr
	 * @param idx
	 * @param prospectiveSymbol
	 * @return
	 */
	private Set<Integer> FIRSTNextStr (List<Integer> expr, int idx, int prospectiveSymbol){
		Set<Integer> res = new HashSet<Integer>();
		if (idx >= expr.size()) {
			res.add(prospectiveSymbol);
			return res;
		}
		//当前符号是终结符
		if (this.isT(expr.get(idx))) {
			res.add(expr.get(idx));
			return res;
		}
		res.addAll(First[expr.get(idx)]);
		//如若存在 epsilon 
		if (res.contains(this.epsilon)) {
			res.remove(this.epsilon);
			res.addAll(this.FIRSTNextStr(expr, idx + 1, prospectiveSymbol));
		}return res;
	}
	
	/*
	CC0 <- closure({[S' -> ·S,eof]}) //构建初始状态集
	CC <- {CC0}		//将初始状态集添加到规范族CC中
	while (new set are still being added to CC)		
		for each unmarked set CCi ∈ CC	//unmarked : 未标记的
			mark CCi as processed	//将CCi标记为处理过的
			for each x following a · in an item in CCi  //对于CCi中项a ·后面的每个x
				temp <- goto(CCi, x)
				if temp ∉ CC
					then CC <- CC ∪ {temp}
				record transition from CCi to temp on x
	*/
	/*
	 因为最后生成Action表中需要规约 reduce A - > BC 
	 所以需要找到这个表达式的序号为了方便弄一个前缀数组
	 记录在前i个产生式中有多少个表达式。
	 */
	int[] preArr;
	
	private void initPreArr() {
		this.preArr = new int[this.production.size()];
		if (this.preArr.length > 0) {
			this.preArr[0] = this.production.get(0).expr.size();
			for (int i = 1; i < this.preArr.length; i++) {
				this.preArr[i] = this.preArr[i - 1] + this.production.get(i).expr.size();
			}
		}
	}
	public void toLRTable() {
		//初始化。
		this.initPreArr();
		this.FIRSTAllSymbol(); 
		Set<String> CC0 = new HashSet<String>();
		List<List<Integer>> expr = this.production.get(startIndex).expr;
		for (int i = 0; i < expr.size(); i++) {
			CC0.add(this.startIndex + BnfContainer.separationCharacter + i + BnfContainer.separationCharacter + 0 + BnfContainer.separationCharacter + this.eof);
		}
		this.closure(CC0);
		CC = new ArrayList<Set<String>>();
		CC.add(CC0);
		int begin = 0;
		int lastSize = -1;
		List<Node> res = new ArrayList<Node>();
		int endState = -1;
		while (lastSize != CC.size()) {
			lastSize = CC.size();
			for (int i = begin; i < lastSize; i++) {
				Set<String> s = this.CC.get(i);
				for (String item : s) {
					String[] strs = item.split(BnfContainer.separationCharacter); // ! 为分隔符
					int productionIdx = Integer.parseInt(strs[0]); //产生式下标
					int exprIdx = Integer.parseInt(strs[1]); //表达式下标
					int placeholder = Integer.parseInt(strs[2]); //占位符下标 这个下标从0开始(表示左侧无语法符号)。
					int prospectiveSymbol = Integer.parseInt(strs[3]);//前瞻符
					List<Integer> list = this.production.get(productionIdx).expr.get(exprIdx);
					if (placeholder < list.size()) {
						//因为对于每个项集的每个项的前瞻符都会进行一次推导,所以这里包含所有的推导。我们只需要记录下来就可以生成表了。
						int x = list.get(placeholder);
						Set<String> temp = this.go(s, x);
						int CCj = this.CCcontainsTheSet(temp);
						if (CCj == -1) {
							CC.add(temp);
							CCj = this.CC.size() - 1;
						}
						res.add(new Node(i, x, CCj));
					}
					//可归约状态
					else {
						res.add(new Node(i, prospectiveSymbol, ((productionIdx - 1 >= 0 ? this.preArr[productionIdx - 1] : 0) + exprIdx + 1) | MASK));
						if (productionIdx == this.startIndex) {
							endState = i;
						}
					}
				}
				//更新begins
				begin = lastSize;
			}
		}
		this.createActionAndGotoTable(res, endState);
	}
	
	/**
	 * 这是构建表时临时记录数据的结构
	 */
	class Node{
		int state;
		/**
		 * 对于sym来说就是终结符和非终结符的编码
		 * 也是利用这个来区别到底把val放Action
		 * 表还是Goto表。
		 */
		int sym;
		/**
		 * 对于val来说
		 * 如若是产生式规约,则将产生式的下标 | MASK作为val
		 * 如若是正常的状态转移,则直接输入转移状态的下标。
		 */
		int val;
		
		public Node(int state, int sym, int val){
			this.state = state;
			this.sym = sym;
			this.val = val;
		}
	}
	/**
	 * 利用这个方法去看规范族CC中是否存在set
	 * 并且会返回set在CC的下标如若存在的话
	 * @param set
	 * @return
	 */
	private int CCcontainsTheSet (Set<String> set) {
		for (int i = 0; i < CC.size(); i++) {
			Set<String> s = CC.get(i);
			if (s.size() == set.size() && set.containsAll(s)) {
				return i;
			}
		}return -1;
	}
	/*
	for each CCi ∈ CC
		for each  item I ∈ CCi
			if I is [A -> β·cθ,a] and goto (CCi , c) = CCj then
				Action[i,c] <- "shift j"
			else if I is [A -> β·,a] then	//规约
				Action[i,a] <- "reduce A->B"
			else if I is [S'->S·,eof] then	//如若是目标项产生式推导完成状态并且前瞻符号为eof,则为接收状态。
				Action[i,eof] <- "accept"
		for each n ∈ NT				//如若项集CCi跳过一个非终结符n即到达j
			if goto(CCi, n) = CCj then
				Goto[i,n] <- j
	*/
	private void createActionAndGotoTable(List<Node> node, int endState) {
		//竖是状态 横是终结符
		this.Action = new int[this.CC.size()][this.T.size()];
		//赋初始值
		for (int i = this.CC.size() - 1; i >= 0; i--) {
			for (int j = this.T.size() - 1; j >=0; j--) {
				this.Action[i][j] = -1;
			}
		}
		//竖是状态 横是非终结符
		this.Goto = new int[this.CC.size()][this.production.size()];//赋初始值
		for (int i = this.CC.size() - 1; i >= 0; i--) {
			for (int j = this.production.size() - 1; j >=0; j--) {
				this.Goto[i][j] = -1;
			}
		}
		for (Node n : node) {
			//如若跨越的符号是终结符
			if (this.isT(n.sym)) {
				Action[n.state][n.sym & DECODE] = n.val;
			}else {
				Goto[n.state][n.sym] = n.val;
			}
		}
		//将接受状态设为最低值。
		this.Action[endState][this.eof & DECODE] = Integer.MIN_VALUE;
		return;
	}
	
	
	public void printActionAndGotoTable() {
		if (this.Action == null || this.Goto == null) {
			System.out.println("表未生成,请使用toLRTable函数生成表。");
			return;
		}
		//先输出一行终结符
		System.out.println("Action表如下");
		System.out.print("\t");
		for (int i = 0; i < this.T.size(); i++) {
			if (i != (this.epsilon & DECODE)) {
				System.out.print(this.T.get(i) + "\t");
			}
		}
		System.out.print("\n");
		for (int i = 0; i < this.Action.length; i++) {
			// 每行第一个输出i
			System.out.print(i + "\t");
			for (int j = 0; j < this.Action[i].length; j++) {
				if (j != (this.epsilon & DECODE)) {
					if (this.Action[i][j] == -1) {
						System.out.print("err\t");
					} // 规约操作
					else if (this.Action[i][j] == Integer.MIN_VALUE) {
						System.out.print("acc\t");
					} else if ((this.Action[i][j] & MASK) == MASK) {
						System.out.print("r" + (this.Action[i][j] & DECODE) + "\t");
					} else {
						System.out.print("s" + this.Action[i][j] + "\t");
					}
				}
			}
			System.out.print("\n");
		}
		System.out.println("Goto表如下");
		// 先输出一行非终结符
		System.out.print("\t");
		for (int i = 0; i < this.production.size(); i++) {
			System.out.print(this.production.get(i).name + "\t");
		}
		System.out.print("\n");
		for (int i = 0; i < this.Goto.length; i++) {
			// 每行第一个输出i
			System.out.print(i + "\t");
			for (int j = 0; j < this.Goto[i].length; j++) {
				if (this.Goto[i][j] == -1) {
					System.out.print("err\t");
					continue;
				}
				System.out.print("s" + this.Goto[i][j] + "\t");
			}System.out.print("\n");
		}
	}
}

/**
 * 代码分析器 可以将代码转换为信息等价的数据结构
 */
class CodeAnalyzer {
	class Token{
		boolean isNt;
		String name;
		public Token (boolean isNt, String name) {
			this.isNt = isNt;
			this.name = name;
		}
	}
	private char[] text;
	private int textSize = 0; //字符串有效长度
	private int point = 0; //text解析进度的指针
	private BnfContainer bc;
	private Token token;
	String left; //左侧非终结符
	private int count = 0; //记录当前已经解析到哪个产生式了
	public CodeAnalyzer (String text, BnfContainer bc) {
		this.bc = bc;
		//初始化代码分析器
		this.initText(text);
		this.initStartSymbol();
		this.initCodeAnalyzer();
	}
	/**
	 * 输入字符串文本,返回处理完毕的字符数组。
	 * @param s
	 * @return
	 */
	private void initText(String s) {
		this.text = s.toCharArray();
		int idx = 0;
		//将字符串变为一个紧凑的字符数组(去除一些妨碍的字符)
		while (idx < text.length) {
			if (text[idx] == '\r' || text[idx] == '\n' || text[idx] == '\t' || text[idx] == ' ') {
				idx++;
			}else {
				text[textSize++] = text[idx++];
			}
		}
	}

	private void initStartSymbol() {
		// 验证是否存在start:<
		point = 0;
		char[] needle = { 's', 't', 'a', 'r', 't', ':', '<' };
		if (textSize <= needle.length) {
			this.notFindStartNT();
		}
		point = 0;
		while (point < needle.length) {
			if (needle[point] == text[point]) {
				point++;
			} else {
				this.notFindStartNT();
			}
		}
		point = needle.length;
		while (point < textSize && text[point] != '>') {
			point++;
		}
		this.bc.setStart(new String(text, needle.length, point - needle.length));
		this.skip(Type.RT);
		this.skip(Type.SEMICOLON);
	}
	/**
	 * 通过skip来跳过字符
	 */
	enum Type{
		LT, //左尖括号
		RT, //右尖括号
		SEMICOLON, //分号
		QUOTE, //双引号
		OR, //或
		COLON, // :
		EQ, //等于号
	}
	private void skip (Type t) {
		switch(t) {
		case LT:
			this.skip('<');
			break;
		case RT:
			this.skip('>');
			break;
		case OR:
			this.skip('|');
			break;
		case SEMICOLON:
			this.skip(';');
			break;
		case QUOTE:
			this.skip('"');
			break;
		case COLON:
			this.skip(':');
			break;
		case EQ:
			this.skip('=');
			break;
		}
	}
	private void skip (char c) {
		if (point >= this.textSize || this.text[point] != c) {
			System.out.println("第" + this.count + "个产生式,缺少符号  " + c);
			System.exit(-1);
		}
		point++;
	}
	/**
	 * 报错 : 没有找到目标(开始)非终结符号! 并退出程序。
	 */
	private void notFindStartNT() {
		System.out.println("没有找到目标非终结符号!");
		System.exit(-1);
	}

	/**
	 * 之所以一开始就要添加非终结符,而不在解析BNF时候添加
	 * 是因为,非终结符存在定义的问题,如若 没有定义
	 * 但有使用(只在右侧出现,未在左侧定义),这个就是错误的。
	 */
	private void initCodeAnalyzer() {
		int idx = this.point;
		this.point = 0;
		this.count = 0;
		while (true) {
			while (this.point < textSize && text[this.point] != ';') {
				this.point++;
			}this.point++;
			this.count++;
			//如若分号后面没有左括号
			if (this.point >= textSize) {
				break;
			}
			String name = this.getNT();
			bc.addNT(name);
		}this.count = 0;
		this.point = idx;
	}

	/**
	 * BNF
	 * 从point开始解析字符串。
	 * <Goal> ::= {<Production>}
	 * <Production> ::= <左侧非终结符> "::=" <Expr>;
	 * <Expr> ::= <Term> { "|" <Term>}";";
	 * <Term> ::= {<Factor>}; 	//Term在这就是多个终结符或非终结符相连接
	 * <Factor> ::= <T> | <NT>
	 */
	public void analyze() {
		while (point < this.textSize) {
			this.count++;
			production();
		}
	}
	
	public void production(){
		//先跳过左侧非终结符
		this.left = this.getNT();
		this.skipDefineSymol();
		this.expr();
	}
	/**
	 * 跳过 ::=
	 */
	public void skipDefineSymol() {
		skip(Type.COLON);
		skip(Type.COLON);
		skip(Type.EQ);
	}
	/**
	 * 获取非终结符
	 * <xxx>
	 */
	public String getNT () {
		skip(Type.LT);
		StringBuilder res = new StringBuilder();
		while (this.point < this.textSize && text[this.point] != '>') {
			res.append(text[this.point++]);
		}
		skip(Type.RT);
		return res.toString();
	}
	
	/**
	 * 当前指针指向 "T" 中第一个"
	 * @return
	 */
	public String getT() {
		this.skip(Type.QUOTE);
		StringBuilder res = new StringBuilder();
		while (this.point < this.textSize && this.text[this.point] != '"') {
			res.append(text[this.point++]);
		}
		this.skip(Type.QUOTE);
		return res.toString();
	}
	
	/**
	 * 当前指针指向 ::= <T>... 中 = 后一个符号
	 */
	public void expr(){
		this.term();
		while (this.point < this.textSize && text[this.point] == '|') {
			this.skip(Type.OR);
			term();
		}this.skip(Type.SEMICOLON);
	}
	
	/**
	 * 如若还有符号,当前符号指向 终结符或非终结符的符号  < 或者 "
	 */
	public void term(){
		//创建一个属于当前term的链表
		bc.creatNewExper(this.left);
		while (this.point < this.textSize && (text[this.point] == '"' || text[this.point] == '<')) {
			factor();
			bc.addExpeElement(this.left, token.isNt, token.name);
		}
	}
	
	/**
	 * 通过factor获取token
	 */
	public void factor(){
		//非终结符
		if (text[this.point] == '"') {
			String name = this.getT(); 
			this.token = new Token(false, name);
		}else {
			String name = this.getNT();
			token = new Token (true, name);
		}
	}
}