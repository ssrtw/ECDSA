#include <iostream>
#include <vector>
using namespace std;

class P {
public:
	int x, y;
	P() :x(0), y(0) {}
	P(int x, int y) :x(x), y(y) {}
	P clone() {
		return P{ x,y };
	}
};

typedef struct ECCcoeff {
	int p, a, b;
}ECCcoeff;

typedef struct PubKey {
	int p, a, b, q;
	P A, B;
}PubKey;

typedef struct Sign {
	int r, s;
}Sign;

class ECC {
private:
	int a, b, p;
	/// <summary>
	/// 利用擴展歐幾里得演算法，遞迴找乘法反元素
	/// </summary>
	int egcd(int a, int b, int r0, int r1) {
		if (b == 1) return r1;
		return egcd(b, a % b, r1, r0 - r1 * (a / b));
	}
public:
	ECC() :a(0), b(0), p(0) {}
	ECC(int a, int b, int p) :a(a), b(b), p(p) {}
	ECC(ECCcoeff coeff) :a(coeff.a), b(coeff.b), p(coeff.p) {}
	/// <summary>
	/// 取得x%n的結果，且結果屬於Zn集合
	/// </summary>
	/// <param name="n">正整數：除數</param>
	/// <param name="x">正整數：除數</param>
	/// <returns>回傳x%n的結果(於Zn集合中)</returns>
	int posiMod(int n, int x) {
		if (x < 0)
			while (x < 0)
				x += n;
		else
			x %= n;
		return x;
	}
	/// <summary>
	/// 將egcd包裝起來，不需於參數列填入初始r值
	/// </summary>
	int calcEgcd(int a, int b) {
		if (b < 0)
			b = posiMod(a, b);
		return posiMod(a, egcd(a, b, 0, 1));
	}

	bool add(P* p1, P* p2) {
		int x, y;
		int s;
		if (p1->x == p2->x) {
			if (p1->y == p2->y)
				s = (3 * p1->x * p1->x + a) * calcEgcd(p, 2 * p1->y);
			else
				return true;
		}
		else {
			s = (p2->y - p1->y) * calcEgcd(p, p2->x - p1->x);
		}
		s = posiMod(p, s);
		x = posiMod(p, s * s - p1->x - p2->x);
		y = posiMod(p, s * (p1->x - x) - p1->y);
		p1->x = x;
		p1->y = y;
		return false;
	}

	ECCcoeff getCoeff() {
		return ECCcoeff{ p,a,b };
	}
};

class CyclicGroup {
public:
	int order;
	vector<P> points;
	CyclicGroup() :order(1) {
		points.clear();
	}
	CyclicGroup(P p1, ECC ecc) :CyclicGroup() {
		bool isOrder;
		P p2 = { p1.x,p1.y };
		points.push_back(p2);
		while (order++) {
			isOrder = ecc.add(&p1, &p2);
			points.push_back(P{ p1.x,p1.y });
			if (isOrder) break;
		}
		points.resize(order - 1);
	}
	P* getP(int idx) {
		if (idx < order)
			return &points[idx - 1];
		else
			return nullptr;
	}
	void printGroup() {
		int col = 0;
		for (int i = 0; i < order - 1; i++) {
			if (!col)
				printf("|");
			printf("%3d|(%3d,%3d)|", i + 1, points[i].x, points[i].y);
			col++;
			if (col == 3) {
				printf("\n");
				col = 0;
			}
		}
		printf("|%3d|( θ, θ)|\n", order);
		if (!col) {
			printf("\n");
		}
	}
};

class ECDSA {
public:
	P* A, * B;
	int privateKey, hashMsg, kE;
	CyclicGroup cg1, cg2;
	ECC ecc;
	PubKey pubKey;
	ECDSA() : hashMsg(0), privateKey(0), kE(0), A(nullptr), B(nullptr) {}
	ECDSA(int privateKey, int hashMsg, int kE, P* A, ECC ecc) : privateKey(privateKey), hashMsg(hashMsg), kE(kE), ecc(ecc), cg1(CyclicGroup(*A, ecc)), A(A), B(nullptr) { }
	PubKey getPubKey() {
		// 冒號後的語法糖已將cg1計算完，就能直接拿到新的
		printf("---------CyclicGroup point A---------\n");
		// 列印點A的群
		cg1.printGroup();
		B = cg1.getP(privateKey);
		// 同時計算B的
		printf("---------CyclicGroup point B---------\n");
		cg2 = CyclicGroup(B->clone(), ecc);
		cg1.printGroup();
		printf("---------簽章---------\n");
		ECCcoeff coeff = ecc.getCoeff();
		PubKey pubKey = { coeff.p,coeff.a,coeff.b,cg1.order,*A,*B };
		printf("公鑰(p,a,b,q,A,B) = (%d,%d,%d,%d,(%d, %d),(%d, %d))\n",
			coeff.p, coeff.a, coeff.b, cg1.order, A->x, A->y, B->x, B->y);
		return pubKey;
	}

	Sign Signature() {
		P* R = cg1.getP(kE);
		int r = R->x, s = ecc.posiMod(cg1.order, (hashMsg + privateKey * r) * ecc.calcEgcd(cg1.order, kE));
		printf("簽章(r, s) = (%d, %d)\n", r, s);
		return Sign{ r,s };
	}

	bool Verify(PubKey pubKey, Sign sign) {
		printf("---------驗證---------\n");
		int w = ecc.calcEgcd(pubKey.q, sign.s);
		int u1 = ecc.posiMod(pubKey.q, w * hashMsg);
		int u2 = ecc.posiMod(pubKey.q, w * sign.r);
		P pointP = cg1.getP(u1)->clone();
		ecc.add(&pointP, cg2.getP(u2));
		printf("w  = %d\nu1 = %d\nu2 = %d\nP  = ( %d, %d)\n", w, u1, u2, pointP.x, pointP.y);
		printf("P.x ≡ %d(mod %d),r ≡ %d(mod %d)\n", pointP.x, pubKey.q, sign.r, pubKey.q);
		if (ecc.posiMod(pubKey.q, pointP.x) == ecc.posiMod(pubKey.q, sign.r))
			return true;
		else 
			return false;
	}
};

int main() {
	ECC ecc = ECC(2, 2, 17);
	P* p1 = new P{ 5,1 };
	ECDSA solution = ECDSA(7, 26, 10, p1, ecc);
	PubKey pubKey = solution.getPubKey();
	Sign sign = solution.Signature();
	bool verify = solution.Verify(pubKey, sign);
	if (verify)
		printf("驗證成功\n");
	else
		printf("驗證失敗\n");
}