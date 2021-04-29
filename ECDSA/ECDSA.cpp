#include <iostream>
#include <iomanip>
#include <vector>
#include "bigint/BigIntegerLibrary.hh"
using namespace std;

class P {
public:
	BigInteger x, y;
	P() :x(0), y(0) {}
	P(BigInteger x, BigInteger y) :x(x), y(y) {}
	P clone() {
		return P(x, y);
	}
};

typedef struct ECCcoeff {
	BigInteger p, a, b;
}ECCcoeff;

typedef struct PubKey {
	BigInteger p, a, b, q;
	P A, B;
}PubKey;

typedef struct Sign {
	BigInteger r, s;
}Sign;

class ECC {
private:
	BigInteger a, b, p;
	static BigInteger egcd(BigInteger a, BigInteger b, BigInteger r0, BigInteger r1);
public:
	ECC() :a(0), b(0), p(0) {}
	ECC(BigInteger a, BigInteger b, BigInteger p) :a(a), b(b), p(p) {}
	ECC(ECCcoeff coeff) :a(coeff.a), b(coeff.b), p(coeff.p) {}

	bool add(P* p1, P* p2) {
		BigInteger x, y;
		BigInteger s;
		if (p1->x == p2->x) {
			if (p1->y == p2->y)
				s = (p1->x * p1->x * 3 + a) * calcEgcd(p, p1->y * 2);
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
	static BigInteger posiMod(BigInteger n, BigInteger x);
	static BigInteger calcEgcd(BigInteger a, BigInteger b);
};

/// <summary>
/// 利用擴展歐幾里得演算法，遞迴找乘法反元素
/// </summary>
BigInteger ECC::egcd(BigInteger a, BigInteger b, BigInteger r0, BigInteger r1) {
	if (b.isZero())
		throw exception("Can't find multiply inverse");
	if (b == 1) return r1;
	return egcd(b, a % b, r1, r0 - r1 * (a / b));
}

/// <summary>
/// 取得x%n的結果，且結果屬於Zn集合
/// </summary>
/// <param name="n">正整數：除數</param>
/// <param name="x">正整數：除數</param>
/// <returns>回傳x%n的結果(於Zn集合中)</returns>
BigInteger ECC::posiMod(BigInteger n, BigInteger x) {
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
BigInteger ECC::calcEgcd(BigInteger a, BigInteger b) {
	try {
		if (b < 0)
			b = posiMod(a, b);
		return posiMod(a, egcd(a, b, 0, 1));
	}
	catch (exception e) {
		cerr << e.what();
		exit(1);
	}
}

class CyclicGroup {
public:
	BigInteger order;
	vector<P> points;
	CyclicGroup() :order(1) {
		points.clear();
	}
	CyclicGroup(P p1, ECC ecc) :CyclicGroup() {
		bool isOrder;
		P p2 = { p1.x,p1.y };
		points.push_back(p2);
		while (true) {
			order++;
			isOrder = ecc.add(&p1, &p2);
			points.push_back(P{ p1.x,p1.y });
			if (isOrder) break;
		}
		points.resize(order.toInt() - 1);
	}
	P* getP(BigInteger idx) {
		if (idx.isZero())
			throw exception("Vector element index invalid");
		if (idx.toInt() < order.toInt())
			return &points[idx.toInt() - 1];
		else
			return nullptr;
	}
	void printGroup() {
		BigInteger col = 0;
		for (int i = 0; i < order.toInt() - 1; i++) {
			if (!col.toInt())
				printf("|");
			cout << setw(3) << right << i + 1 << "|("
				<< setw(3) << right << points[i].x << ","
				<< setw(3) << right << points[i].y << ")|";
			col++;
			if (col == 3) {
				printf("\n");
				col = 0;
			}
		}
		cout << "|" << setw(3) << right << order << "|( θ, θ)|\n";
		if (!col.toInt()) {
			printf("\n");
		}
	}
};

class ECDSA {
public:
	P* A, * B;
	BigInteger privateKey, hashMsg, kE;
	CyclicGroup cg1, cg2;
	ECC ecc;
	PubKey pubKey;
	ECDSA() : hashMsg(0), privateKey(0), kE(0), A(nullptr), B(nullptr) {}
	ECDSA(BigInteger privateKey, BigInteger hashMsg, BigInteger kE, P* A, ECC ecc) : privateKey(privateKey), hashMsg(hashMsg), kE(kE), ecc(ecc), cg1(CyclicGroup(*A, ecc)), A(A), B(nullptr) { }
	PubKey getPubKey() {
		// 冒號後的語法糖已將cg1計算完，就能直接拿到新的
		cout << "---------CyclicGroup point A---------\n";
		// 列印點A的群
		cg1.printGroup();
		B = cg1.getP(privateKey);
		// 同時計算B的
		cout << "---------CyclicGroup point B---------\n";
		cg2 = CyclicGroup(B->clone(), ecc);
		cg1.printGroup();
		cout << "---------簽章---------\n";
		ECCcoeff coeff = ecc.getCoeff();
		PubKey pubKey = { coeff.p,coeff.a,coeff.b,cg1.order,*A,*B };
		cout << "公鑰(p,a,b,q,A,B) = (" << coeff.p << ","
			<< coeff.a << ","
			<< coeff.b << ","
			<< cg1.order << ",("
			<< A->x << ","
			<< A->y << "),("
			<< B->x << ","
			<< B->y << "))\n";
		return pubKey;
	}

	Sign Signature() {
		P* R = cg1.getP(kE);
		BigInteger tmp1 = (hashMsg + privateKey * R->x);
		BigInteger tmp2 = ecc.calcEgcd(cg1.order, kE);
		BigInteger r = R->x, s = ecc.posiMod(cg1.order, tmp1 * tmp2);
		cout << "簽章(r, s) = ("
			<< r << ","
			<< s << ")\n";
		return Sign{ r,s };
	}

	bool Verify(PubKey pubKey, Sign sign) {
		cout << "---------驗證---------\n";
		BigInteger w = ecc.calcEgcd(pubKey.q, sign.s);
		BigInteger u1 = ecc.posiMod(pubKey.q, w * hashMsg);
		BigInteger u2 = ecc.posiMod(pubKey.q, w * sign.r);
		P pointP = cg1.getP(u1)->clone();
		ecc.add(&pointP, cg2.getP(u2));
		cout << "w  = " << w << "\nu1 = "
			<< u1 << "\nu2 = "
			<< u2 << "\nP  = ( "
			<< pointP.x << ", "
			<< pointP.y << ")\n";
		cout << "P.x ≡ " << pointP.x << "(mod "
			<< pubKey.q << "),r ≡ "
			<< sign.r << "(mod "
			<< pubKey.q << ")\n";
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