package cn.vizdl.parseTree;

import java.util.LinkedList;

/**
 * Leetcode 224. 基本计算器
 * 2019年7月12日20:43:56
 * @author HP
 *
 */

public class Demo001 {
    /**
	 * token元素类型包含 + - * / ( ) 整型数字
	 */
	public enum Type {  
		PLUS, MINUS, MUL, DIV, LPAREN, RPAREN, INTEGER
	} 
	/**
	 * TokenNode是一个双向链表节点
	 */
	class TokenNode{
		public int val;
		public Type type;
		
		public TokenNode(Type type) {
			this.type = type;
		}
		
		public TokenNode(int val, Type type) {
			this.val = val;
			this.type = type;
		}
	}
	class TreeNode{
		public TokenNode val;
		public TreeNode left;
		public TreeNode right;
		
		public TreeNode (TokenNode val) {
			this.val = val;
		}
		
	}
	/**
	 * 将优先级编入CFG,通过构建语法分析树,后根序遍历求值。
	 * 字符串表达式可以包含左括号 ( ，右括号 )，加号 + ，减号 -，非负整数和空格  。
	 * 第一步 : 有多少个优先级？
	 * 有三个优先级
	 * 第二步 : 优先级分别包含什么
	 * 最高优先级 : ()
	 * 普通优先级 : * /
	 * 最低优先级 : + -
	 * 第三步 : 书写CFG表达式
	 * <Goal> ::= <Expr>
	 * <Expr> ::= <Expr> <+> <Term>
	 * 		| <Expr> <-> <Term>
	 * 		| <Expr>
	 * <Term> ::= <Term> <*> <Factor>
	 * 		| <Temp> </> <Factor>
	 * 		| <Temp>
	 * <Factor> ::= <(> <Expr> <)>
	 * 		| <num>
	 * 第四步 : 消除左递归
	 * 	
	 * 第五步 : 将字符串转换为token链表
	 * 第六步 : 将token链表转换为语法分析树
	 * @param s
	 * @return
	 */
	LinkedList<TokenNode> list;
	public int calculate(String s) {
		list = new LinkedList<TokenNode>();
		char[] ch = s.toCharArray();
		this.stringToTokenList(ch);
		TreeNode root = this.tokenListToTree();
		return this.eval(root);
    }
	
	/**
	 * 将字符串s的信息转换入list内
	 * @param s
	 */
	private void stringToTokenList (char[] ch) {
		int idx = 0;
		while (idx < ch.length) {
            if (ch[idx] == ' '){
                idx++;
            }else if (ch[idx] == '+') {
				list.add(new TokenNode(Type.PLUS)); idx++;
			}else if (ch[idx] == '-') {
				list.add(new TokenNode(Type.MINUS)); idx++;
			}else if (ch[idx] == '*') {
				list.add(new TokenNode(Type.MUL)); idx++;
			}else if (ch[idx] == '/') {
				list.add(new TokenNode(Type.DIV)); idx++;
			}else if (ch[idx] == '(') {
				list.add(new TokenNode(Type.LPAREN)); idx++;
			}else if (ch[idx] == ')') {
				list.add(new TokenNode(Type.RPAREN)); idx++;
			}else {
				int count = 0;
				while (idx + count < ch.length && ch[idx + count] >= '0' && ch[idx + count] <= '9') {
					count++;
				}
				String s = new String(ch, idx, count);
				idx += count;
				int val = Integer.parseInt(s);
				list.add(new TokenNode(val, Type.INTEGER));
			}
		}
	}
	 //point是list的指针
	int point;
	private TreeNode tokenListToTree() {
		point = 0;
		return expr();
	}
	/*
	e.g. 1+2+3+4
	this will first create
	  +
	  /\
	 1  2
	then, add + 3 at the top, 
	     +
		/\
	   +  3
	  /\
	 1  2
	1+2*3 like
	   +
	   /\
      1   *
	      /\
		 2  3
    because plus->right = term(), and term is 2*3
	*/
	/*
	 只有终结符才point++;
	 */
	//对于expr来说,就是两项或多项进行相加减。
	private TreeNode expr() {	
		TreeNode left = term();
		
		while (point < list.size() && (list.get(point).type == Type.PLUS || list.get(point).type == Type.MINUS)) {
			TreeNode root = new TreeNode(list.get(point++));
			TreeNode right = term();
			root.left = left;
			root.right = right;
			left = root;
		}return left;
	}
	//对于term来说,就是两项或多项进行相乘除
	//从 * 或者 / 符号前一个符号开始
	private TreeNode term() {	
		TreeNode left = factor();
		
		while (point < list.size() && (list.get(point).type == Type.DIV || list.get(point).type == Type.MUL)) {
			TreeNode root = new TreeNode(list.get(point++));
			TreeNode right = factor();
			root.left = left;
			root.right = right;
			left = root;
		}return left;
	}

	private TreeNode factor() {
		if (list.get(point).type == Type.LPAREN) {
			point++;	//跳过左括弧
			TreeNode res = expr();
			point++;	//跳过右括弧
			return res;
		}else {
			return new TreeNode(list.get(point++));
		}
	} 
	
	private int eval(TreeNode root) {
		if (root == null)
			return 0;
		Type type = root.val.type;
		if (type == Type.INTEGER)
			return root.val.val;
		int left = eval(root.left);
		int right = eval(root.right);
		if (type == Type.PLUS) {
			return left + right;
		}else if (type == Type.MINUS) {
			return left - right;
		}else if (type == Type.MUL) {
			return left * right;
		}else{
			return left / right;
		}
	}
}
