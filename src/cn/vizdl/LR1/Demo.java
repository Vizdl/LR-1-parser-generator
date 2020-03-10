package cn.vizdl.LR1;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Scanner;

/*
项目名 :  LR(1) parser generator (LR(1)语法分析器生成器)
项目分析 : 
	输入 : 输入某文件内存地址。且内部采用  <Expr> ::=  <Term> + <Factor>; 的结构输入的LR(1)语法。
	这里的仅支持 BNF范式内部的 终结符,非终结符,或运算,;(表示产生式结束),::=(表示为定义为)
	在这里不支持闭包,也就是{},因为闭包可以转换为非终结符的递归。
		输入文本格式 :
			start : <aim_name>  //aim_name表示起始符号名称 
		例子 : 
			start : <Goal>;
			<Goal> ::= <Expr>;
			<Expr> ::= <Expr> "+" <Term> | <Expr> "-" <Term>;
			<Term> ::= <Term> "*" <Factor> | <Term> "/" <Factor>;
			<Factor> ::= "number";
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
	输出 ：Action 和 GoTo 表。 
*/ 
public class Demo {
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
		//
		BnfContainer bc = new BnfContainer();
		CodeAnalyzer ca = new CodeAnalyzer(s, bc);
		ca.analyze();
		bc.printBNF();
		
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
	public BnfContainer() {
		//内部数据结构初始化
		NTMap = new HashMap<String,Integer>();
		TMap = new HashMap<String,Integer>();
		T = new ArrayList<String>();
		production = new ArrayList<NTNode>();
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
//System.out.println(name);
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
	}
}

/**
 * 代码分析器
 * 可以将代码转换为信息等价的数据结构
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
