package test;

public class Test {
	protected Test f, next;
	// Phase 1 Public Testcases
	private static Test public_01() {
		Test a = new Test();
		// a: {new7}
		Test b = new Test();
		// a: {new7}, b: {new9}
		b.f = a;
		// a: {new7}, b: {new9}, new9.f: {new7}
		return a;
	}

	private static void public_02(int value) {
		Test a = new Test();
		// a: {new17}
		Test b = new Test();
		// a: {new17}, b: {new19}
		b.f = b;
		// a: {new17}, b: {new19}, new19.f: {new19}
		if(value <= 100) {
			// a: {new17}, b: {new19}, new19.f: {new19}
			b.f = a;
			// a: {new17}, b: {new19}, new19.f: {new17}
		}
		else {
			// a: {new17}, b: {new19}, new19.f: {new19}
			b.f = null;
			// a: {new17}, b: {new19}, new19.f: {null}
		}
		// a: {new17}, b: {new19}, new19.f: {null, new17}
	}

	private static void public_03(int value) {
		Test a = new Test();
		// a: {new37}
		Test b = new Test();
		// a: {new37}, b: {new39}
		Test c = new Test();
		// a: {new37}, b: {new39}, c: {new41}
		b.f = c;
		// a: {new37}, b: {new39}, c: {new41}, new39.f: {new41}
		while(value < 100) {
			// a: {new37}, b: {new39, new41, new47}, c: {new41}, new39.f: {new41, new47}, new41.f: {new47}, new47.f: {new47}
			b.f = new Test();
			// a: {new37}, b: {new39, new41, new47}, c: {new41}, new39.f: {new41, new47}, new41.f: {new47}, new47.f: {new47}
			b = b.f;
			// a: {new37}, b: {new41, new47}, c: {new41}, new39.f: {new41, new47}, new41.f: {new47}, new47.f: {new47}
			value += 1;
			// a: {new37}, b: {new41, new47}, c: {new41}, new39.f: {new41, new47}, new41.f: {new47}, new47.f: {new47}
		}
		// a: {new37}, b: {new39, new41, new47}, c: {new41}, new39.f: {new41, new47}, new41.f: {new47}, new47.f: {new47}
		c.f = b.f;
		// a: {new37}, b: {new39, new47}, c: {new41}, new39.f: {new41, new47}, new41.f: {new41, new47}
	}

	@SuppressWarnings("null")
	private static void public_04(int value) {
		Test a = null;
		// a: {null}
		Test b = new Test();
		// a: {null}, b: {new63}
		Test c = new Test();
		// a: {null}, b: {new63}, c: {new65}
		Test d = new Test();
		// a: {null}, b: {new63}, c: {new65}, d: {new67}
		b.f = null;
		// a: {null}, b: {new63}, c: {new65}, d: {new67}, new63.f: {null}
		c.f = d;
		// a: {null}, b: {new63}, c: {new65}, d: {new67}, new63.f: {null}, new65.f: {new67}
		if(value == 100) {
			// a: {null}, b: {new63}, c: {new65}, d: {new67}, new63.f: {null}, new65.f: {new67}
			a = b;
			// a: {new63}, b: {new63}, c: {new65}, d: {new67}, new63.f: {null}, new65.f: {new67}
		}
		else if (value == 200) {
			// a: {null}, b: {new63}, c: {new65}, d: {new67}, new63.f: {null}, new65.f: {new67}
			a = c;
			// a: {new65}, b: {new63}, c: {new65}, d: {new67}, new63.f: {null}, new65.f: {new67}
		}
		else {
			// a: {null}, b: {new63}, c: {new65}, d: {new67}, new63.f: {null}, new65.f: {new67}
			a = null;
			// a: {null}, b: {new63}, c: {new65}, d: {new67}, new63.f: {null}, new65.f: {new67}
		}
		// a: {null, new63, new65}, b: {new63}, c: {new65}, d: {new67}, new63.f: {null}, new65.f: {new67}

		Test m = a.f;
		// a: {null, new63, new65}, b: {new63}, c: {new65}, d: {new67}, new63.f: {null}, new65.f: {new67}, m: {null, new67}
		Test n = new Test();
		// a: {null, new63, new65}, b: {new63}, c: {new65}, d: {new67}, new63.f: {null}, new65.f: {new67}, m: {null, new67}, n: {new92}
		a.f = n;
		// a: {null, new63, new65}, b: {new63}, c: {new65}, d: {new67}, new63.f: {null, new92}, new65.f: {new67, new92}, m: {null, new67}, n: {new92}
		m = a.f;
		// a: {null, new63, new65}, b: {new63}, c: {new65}, d: {new67}, new63.f: {null, new92}, new65.f: {new67, new92}, m: {null, new67, new92}, n: {new92}
	}

	private static void public_05(int i) {
		int[] a = new int[3];
		// a: {new101}
		int[] b = new int[4];
		// a: {new101}, b: {new103}
		int[] c;
		// a: {new101}, b: {new103}
		if(i > 0) {
			// a: {new101}, b: {new103}
			c = a;
			// a: {new101}, b: {new103}, c: {new101}
		}
		else {
			// a: {new101}, b: {new103}
			c = b;
			// a: {new101}, b: {new103}, c: {new103}
		}
		// a: {new101}, b: {new103}, c: {new101, new103}
		c[0] = 1;
		// a: {new101}, b: {new103}, c: {new101, new103}
	}

	private static void public_06() {
		Test a = new Test();
		// a: {new123}
		Test b = a;
		// a: {new123}, b: {new123}
		Test c = new Test();
		// a: {new123}, b: {new123}, c: {new127}
		Test d;
		// a: {new123}, b: {new123}, c: {new127}
		if(a == b) {
			// a: {new123}, b: {new123}, c: {new127}
			d = a;
			// a: {new123}, b: {new123}, c: {new127}, d: {new123}
		}
		else {
			// a: {new123}, b: {new123}, c: {new127}
			d = c;
			// a: {new123}, b: {new123}, c: {new127}, d: {new127}
		}
		// a: {new123}, b: {new123}, c: {new127}, d: {new123, new127}
		d.f = b;
		// a: {new123}, b: {new123}, c: {new127}, d: {new123, new127}, new123.f: {new123}, new127.f: {new123}
	}

	private static void public_07(int i) {
		Test a = new Test();
		// a: {new147}
		Test b = new Test();
		// a: {new147}, b: {new149}
		Test c;
		// a: {new147}, b: {new149}
		if(i > 0) {
			// a: {new147}, b: {new149}
			b.f = a;
			// a: {new147}, b: {new149}, new149.f: {new147}
		}
		else {
			// a: {new147}, b: {new149}
			b.f = b;
			// a: {new147}, b: {new149}, new149.f: {new149}
		}
		// a: {new147}, b: {new149}, new149.f: {new147, new149}
		if(a == b.f) {
			// a: {new147}, b: {new149}, new149.f: {new147, new149}
			a.f = b.f;
			// a: {new147}, b: {new149}, new147.f: {new147, new149}, new149.f: {new147}
		}
		else {
			// a: {new147}, b: {new149}, new149.f: {new147, new149}
			a.f = b;
			// a: {new147}, b: {new149}, new147.f: {new149}, new149.f: {new149}
		}
		// a: {new147}, b: {new149}, new147.f: {new147, new149}, new149.f: {new147, new149}
		c = a.f;
		// a: {new147}, b: {new149}, new147.f: {new147, new149}, new149.f: {new147, new149}, c: {new147, new149}
	}


	public static class MyInt {
		public int f = 1;
	}

	// Phase 2 Public Testcases
	private static int public_08(int check) {
		//% check: [-inf,inf]
		int x;
		//% check: [-inf,inf], x: [-inf,inf]
		if (check < 10) {
			//% check: [-inf,9], x: [-inf,inf]
			x = 0;
			//% check: [-inf,9], x: [0,0]
		} else {
			//% check: [10,inf], x: [-inf,inf]
			x = 2;
			//% check: [10,inf], x: [2,2]
		}
		//% check: [-inf,inf], x: [0,2]
		int y = 2*x + 5;
		//% check: [-inf,inf], x: [0,2], y: [5,9]
		return y;
	}

	private static void public_09(int n) {
		//% n: [-inf,inf]
		int i = n;
		//% n: [-inf,inf], i: [-inf,inf]
		while (i > 10) {
			//% n: [-inf,inf], i: [11,inf]
			i = i - 1;
			//% n: [-inf,inf], i: [10,inf]
		}
		//% n: [-inf,inf], i: [-inf,10]
		int j = 9;
		//% n: [-inf,inf], i: [-inf,10], j: [9,9]
		int k = 1;
		//% n: [-inf,inf], i: [-inf,10], j: [9,9], k: [1,1]
		while (j < 18) {
			//% n: [-inf,inf], i: [-inf,10], j: [9,17], k: [1,inf]
			j = j + k;
			//% n: [-inf,inf], i: [-inf,10], j: [10,inf], k: [1,inf]
			k = k + 1;
			//% n: [-inf,inf], i: [-inf,10], j: [10,inf], k: [2,inf]
		}
		//% n: [-inf,inf], i: [-inf,10], j: [18,inf], k: [1,inf]
		int l = 0;
		//% n: [-inf,inf], i: [-inf,10], j: [18,inf], k: [1,inf], l: [0,0]
		if (i != j) {
			//% n: [-inf,inf], i: [-inf,10], j: [18,inf], k: [1,inf], l: [0,0]
			l = 2;
			//% n: [-inf,inf], i: [-inf,10], j: [18,inf], k: [1,inf], l: [2,2]
		}
		//% n: [-inf,inf], i: [-inf,10], j: [18,inf], k: [1,inf], l: [2,2]
		k = l;
		//% n: [-inf,inf], i: [-inf,10], j: [18,inf], k: [2,2], l: [2,2]
	}

	private static void public_10(){
		MyInt a = new MyInt();
		// a: {new239}
		//% new239.f: [1,1]
		MyInt b = new MyInt();
		// a: {new239}, b: {new242}
		//% new239.f: [1,1], new242.f: [1,1]
		MyInt c;
		// a: {new239}, b: {new242}, c: {null}
		//% new239.f: [1,1], new242.f: [1,1]
		c = a;
		// a: {new239}, b: {new242}, c: {new239}
		//% new239.f: [1,1], new242.f: [1,1]
		c.f = c.f + 1;
		// a: {new239}, b: {new242}, c: {new239}
		//% i: [-inf,inf], new239.f: [2,2], new242.f: [1,1]
	}

	private static void public_11() {
		Test[] a;
		// a: {null}
		//%
		Test[] b = new Test[3];
		// a: {null}, b: {new260}
		//%
		Test[] c = new Test[10];
		// a: {null}, b: {new260}, c: {new263}
		//%
		if (b[0] == c[1]) {
			// a: {null}, b: {new260}, c: {new263}
			//%
			a = b;
			// a: {new260}, b: {new260}, c: {new263}
			//%
		} else {
			// a: {null}, b: {new260}, c: {new263}
			//%
			a = c;
			// a: {new263}, b: {new260}, c: {new263}
			//%
		}
		// a: {new260, new263}, b: {new260}, c: {new263}
		//%
		int i = 0;
		// a: {new260, new263}, b: {new260}, c: {new263}
		//% i: [0,0]
		while (i < 2) {
			// a: {new260, new263}, b: {new260}, c: {new263}
			//% i: [0,1]
			a[i] = a[i+1];			//# Safe array access
			// a: {new260, new263}, b: {new260}, c: {new263}
			//% i: [0,1]
			i++;
			// a: {new260, new263}, b: {new260}, c: {new263}
			//% i: [1,2]
		}
		// a: {new260, new263}, b: {new260}, c: {new263}
		//% i: [2,2]
		a[i] = a[i+1];				//# Unsafe array access
		// a: {new260, new263}, b: {new260}, c: {new263}
		//% i: [2,2]
	}

	private static void public_12(int x) {
		//% x: [-inf,inf]
		Test[] a = new Test[5];
		// a: {new303}
		//% x: [-inf,inf]
		x = x + 1;
		// a: {new303}
		//% x: [-inf,inf]
		Test b = a[x];				//# Unsafe array access
		// a: {new303}
		//% x: [-inf,inf]
	}

	public static void main(String[] args) {
		/* In case you need to run the main function in the Test class, use the command
		 *		mvn clean package exec:java@test -q
		 */
		System.out.println("Running Test");
		public_01();
		public_02(0);
		public_03(0);
		public_04(100);
		public_05(0);
		public_06();
		public_07(0);
		public_08(0);
		public_09(0);
		public_10();
		public_11();
		public_12(0);
		System.out.println("Completed");
	}
}