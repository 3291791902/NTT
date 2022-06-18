#include <iostream>
#include <algorithm>
#include <cstdio>
#include <cctype>
using namespace std;
typedef long long LL;
const LL MOD = 998244353LL;
const LL INV2 = (MOD + 1) / 2;
const int N = 1 << 18;
inline LL readLL() {
	LL ret = 0;
	int ch = getchar();
	while (!isdigit(ch)) {
		ch = getchar();
	}
	while (isdigit(ch)) {
		ret = ((ret << 3) + (ret << 1) + (ch ^ 48));
		ch = getchar();
	}
	return ret;
}
inline LL my_pow(LL a, LL b) {
	LL ret = 1LL, c = a;
	while (b) {
		if (b & 1) {
			ret = ret * c % MOD;
		}
		c = c * c % MOD;
		b >>= 1;
	}
	return ret;
}
inline LL my_inv(LL a) {
	return my_pow(a, MOD - 2);
}
int rev[N];
void init(int lim) {
	for (int i = 0; i < lim; i++) {
		rev[i] = (i & 1) * (lim >> 1) + (rev[i >> 1] >> 1);
	}
}
void ntt(LL* arr, int lim, int opt) {
	init(lim);
	for (int i = 0; i < lim; i++) {
		if (i < rev[i]) {
			swap(arr[i], arr[rev[i]]);
		}
	}
	for (int w = 2; w <= lim; w <<= 1) {
		int k = w >> 1;
		LL step = my_pow(3, (MOD - 1) / w);
		for (int i = 0; i < lim; i += w) {
			LL now = 1;
			for (int j = 0; j < k; j++) {
				LL temp = arr[i + j + k] * now % MOD;
				arr[i + j + k] = (arr[i + j] - temp + MOD) % MOD;
				arr[i + j] = (arr[i + j] + temp + MOD) % MOD;
				now = now * step % MOD;
			}
		}
	}
	if (opt == -1) {
		reverse(arr + 1, arr + lim);
		LL inv = my_inv(lim);
		for (int i = 0; i < lim; i++) {
			arr[i] = arr[i] * inv % MOD;
		}
	}
}
LL tarr1[N];
void poly_inv(LL* a, LL* b, int lim) {
	b[0] = my_inv(a[0]);
	for (int w = 2; w <= lim; w <<= 1) {
		int k = w >> 1;
		for (int i = 0; i < w; i++) {
			tarr1[i] = a[i];
		}
		int w2 = w << 1;
		for (int i = w; i < w2; i++) {
			tarr1[i] = 0;
		}
		for (int i = k; i < w2; i++) {
			b[i] = 0;
		}
		ntt(b, w2, 1);
		ntt(tarr1, w2, 1);
		for (int i = 0; i < w2; i++) {
			b[i] = (2 * b[i] - b[i] * b[i] % MOD * tarr1[i] % MOD + MOD) % MOD;
		}
		ntt(b, w2, -1);
	}
	int w2 = lim << 1;
	for (int i = lim; i < w2; i++) {
		b[i] = 0;
	}
}
LL tarr2[N], tarr3[N];
void poly_sqrt(LL* a, LL* b, int lim) {
	b[0] = 1;
	for (int w = 2; w <= lim; w <<= 1) {
		int k = w >> 1;
		int w2 = w << 1;
		for (int i = 0; i < w; i++) {
			tarr3[i] = a[i];
		}
		for (int i = w; i < w2; i++) {
			tarr3[i] = 0;
		}
		for (int i = k; i < w2; i++) {
			b[i] = 0;
		}
		poly_inv(b, tarr2, w);
		ntt(tarr2, w2, 1);
		ntt(b, w2, 1);
		ntt(tarr3, w2, 1);
		for (int i = 0; i < w2; i++) {
			b[i] = (tarr3[i] * tarr2[i] % MOD + b[i]) % MOD;
		}
		ntt(b, w2, -1);
		for (int i = 0; i < w; i++) {
			b[i] = b[i] * INV2 % MOD;
		}
	}
	int w2 = lim << 1;
	for (int i = lim; i < w2; i++) {
		b[i] = 0;
	}
}
void poly_diff(LL* a, LL* b, int lim) {
	for (int i = 1; i < lim; i++) {
		b[i - 1] = (i * a[i]) % MOD;
	}
	b[lim - 1] = 0;
}
void poly_int(LL* a, LL* b, int lim) {
	for (int i = lim - 1; i >= 1; i--) {
		b[i] = a[i - 1] * my_inv(i) % MOD;
	}
	b[0] = 0;
}
LL tarr4[N], tarr5[N];
void poly_ln(LL* a, LL* b, int lim) {
	poly_diff(a, tarr4, lim);
	poly_inv(a, tarr5, lim);
	int w2 = lim << 1;
	ntt(tarr4, w2, 1);
	ntt(tarr5, w2, 1);
	for (int i = 0; i < w2; i++) {
		tarr4[i] = tarr4[i] * tarr5[i] % MOD;
	}
	ntt(tarr4, w2, -1);
	poly_int(tarr4, tarr5, lim);
	for (int i = 0; i < lim; i++) {
		b[i] = tarr5[i];
	}
}
LL tarr6[N];
void poly_exp(LL* a, LL* b, int lim) {
	b[0] = 1;
	for (int w = 2; w <= lim; w <<= 1) {
		int w2 = w << 1;
		int k = w >> 1;
		for (int i = k; i < w2; i++) {
			b[i] = 0;
		}
		poly_ln(b, tarr6, w);
		for (int i = 0; i < w; i++) {
			tarr6[i] = (MOD - tarr6[i] + a[i]) % MOD;
		}
		tarr6[0] = (tarr6[0] + 1) % MOD;
		for (int i = w; i < w2; i++) {
			tarr6[i] = 0;
		}
		ntt(tarr6, w2, 1);
		ntt(b, w2, 1);
		for (int i = 0; i < w2; i++) {
			b[i] = b[i] * tarr6[i] % MOD;
		}
		ntt(b, w2, -1);
	}
	int w2 = lim << 1;
	for (int i = lim; i < w2; i++) {
		b[i] = 0;
	}
}
int n;
LL my_arr1[N], my_arr2[N];
int main() {
	ios::sync_with_stdio(false);
	cout.tie(0);
	n = (int)readLL();
	for (int i = 0; i < n; i++) {
		my_arr1[i] = readLL();
	}
	int lim = 1;
	while (lim < n) {
		lim <<= 1;
	}
	//poly_exp(my_arr1, my_arr2, lim);
	for (int i = 0; i < n; i++) {
		cout << my_arr2[i] << ' ';
	}
	cout << endl;
	return 0;
}
