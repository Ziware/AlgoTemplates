#include <cmath>
#include <ctime>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <utility>
#include <vector>
#include <algorithm>
#include <math.h>
#include <iomanip>
#include <map>
#include <set>
#include <cassert>

using namespace std;

#define all(x) (x).begin(), (x).end()
#define rall(x) (x).rbegin(), (x).rend()
#define fi first
#define se second
#define ll long long
#define ld long double

mt19937 rnd(1337);

const ld kInf = 1e12 + 7;
const ld kPi = acosl(-1);
const ld kEps = 1e-10;

bool Equal(ld a, ld b) {
    return abs(a - b) < kEps;
}

int GetSign(ld a) {
    if (Equal(a, 0)) {
        return 0;
    }
    if (a < 0) {
        return -1;
    }
    return 1;
}

inline ld Sqare(ld a) {
    return a * a;
}

ld ToDegree(ld g) {
    ld ang = (180 * g) / kPi;
    return ang;
}

struct Point;
struct Vector;
struct Segment;
struct Line;
struct Ray;
struct Circle;

struct Point {
    ld x, y;
    Point() = default;
    Point(ld x, ld y) : x(x), y(y) {
    }
    explicit Point(const Vector &other);
    Point &operator+=(const Vector &other);
    Point &operator-=(const Vector &other);
    Point operator+(const Vector &other) const;
    Point operator-(const Vector &other) const;
    Point &operator+=(const Point &other) {
        x += other.x;
        y += other.y;
        return *this;
    }
    Point &operator-=(const Point &other) {
        x -= other.x;
        y -= other.y;
        return *this;
    }
    Point operator+(const Point &other) const {
        return Point(x + other.x, y + other.y);
    }
    Point operator-(const Point &other) const {
        return Point(x - other.x, y - other.y);
    }
    bool operator==(const Point &to) const {
        return Equal(x, to.x) && Equal(y, to.y);
    }
    bool operator!=(const Point &to) const {
        return !(*this == to);
    }
    bool operator<(const Point &to) const {
        return x < to.x || (Equal(x, to.x) && y < to.y);
    }
    bool operator>(const Point &to) const {
        return x > to.x || (Equal(x, to.x) && y > to.y);
    }
    Point operator*(ld k) const {
        return Point(x * k, y * k);
    }
    Point operator/(ld k) const {
        assert(k != 0);
        return Point(x / k, y / k);
    }
    Point &operator*=(ld d) {
        x *= d;
        y *= d;
        return *this;
    }
    Point &operator/=(ld k) {
        assert(!Equal(k, 0));
        x /= k;
        y /= k;
        return *this;
    }
    Point operator-() const {
        return Point(-x, -y);
    }
    ld Dist(const Point &other) const {
        return sqrtl((x - other.x) * (x - other.x) + (y - other.y) * (y - other.y));
    }
    ld DistSqare(const Point &other) const {
        return (x - other.x) * (x - other.x) + (y - other.y) * (y - other.y);
    }
    ld Dist(const Line &l) const;
    ld Dist(const Segment &seg) const;
    bool IsValid() const {
        return *this != Point(-kInf, -kInf) && *this != Point(kInf, kInf);
    }
};

const Point kNoIntersection = {-kInf, -kInf};
const Point kInfIntersection = {kInf, kInf};
const Point kZeroPoint = {0, 0};

istream &operator>>(istream &in, Point &p) {
    return (in >> p.x >> p.y);
}

ostream &operator<<(ostream &out, const Point &p) {
    return (out << p.x << " " << p.y);
}

bool YComp(const Point &a, const Point &b) {
    return a.y < b.y || (Equal(a.y, b.y) && a.x < b.x);
}

ld Dist(const Point &a, const Point &b) {
    return a.Dist(b);
}

ld DistSqare(const Point &a, const Point &b) {
    return a.DistSqare(b);
}

// c in [a, b]
bool BoundingBox(ld c, ld a, ld b) {
    return c <= max(a, b) + kEps && c >= min(a, b) - kEps;
}

// Point c in ractangle [a.x, b.x] [a.y, b.y]
bool BoundingBox(const Point &c, const Point &a, const Point &b) {
    return BoundingBox(c.x, a.x, b.x) && BoundingBox(c.y, a.y, b.y);
}

struct Vector {
    ld x, y;
    Vector() = default;
    Vector(const Point &s) : x(s.x), y(s.y) {
    }
    Vector(ld x, ld y) : x(x), y(y) {
    }
    Vector(const Point &s, const Point &f) : x(f.x - s.x), y(f.y - s.y) {
    }
    Vector &operator+=(const Vector &other) {
        x += other.x;
        y += other.y;
        return *this;
    }
    Vector &operator-=(const Vector &other) {
        x -= other.x;
        y -= other.y;
        return *this;
    }
    Vector operator+(const Vector &other) const {
        return Vector(x + other.x, y + other.y);
    }
    Vector operator-(const Vector &other) const {
        return Vector(x - other.x, y - other.y);
    }
    Vector &operator*=(ld d) {
        x *= d;
        y *= d;
        return *this;
    }
    Vector &operator/=(ld k) {
        assert(!Equal(k, 0));
        x /= k;
        y /= k;
        return *this;
    }
    Vector operator*(ld k) const {
        return Vector(x * k, y * k);
    }
    Vector operator/(ld k) const {
        assert(!Equal(k, 0));
        return Vector(x / k, y / k);
    }
    Vector operator-() const {
        return Vector(-x, -y);
    }

    ld SquareLen() const {
        return x * x + y * y;
    }
    ld Len() const {
        return sqrtl(SquareLen());
    }
    Vector &Normal() {
        ld del = Len();
        x /= del;
        y /= del;
        return *this;
    }
    ld Dot(const Vector &other) const {
        return (x * other.x + x * other.y);
    }
    ld Cross(const Vector &other) const {
        return (x * other.y - other.x * y);
    }
    ld GetAngle() const {
        ld a = atan2(y, x);
        if (a < 0) {
            a += 2 * kPi;
        }
        return a;
    }
    ld GetAngle(const Vector &v) const {
        ld a = atan2(Cross(v), Dot(v));
        if (a < 0) {
            a += 2 * kPi;
        }
        return a;
    }
};

Point::Point(const Vector &other) : x(other.x), y(other.y){};
Point &Point::operator+=(const Vector &other) {
    x += other.x;
    y += other.y;
    return *this;
}
Point &Point::operator-=(const Vector &other) {
    x -= other.x;
    y -= other.y;
    return *this;
}
Point Point::operator+(const Vector &other) const {
    return Point(x + other.x, y + other.y);
}
Point Point::operator-(const Vector &other) const {
    return Point(x - other.x, y - other.y);
}

ld Dot(const Vector &s, const Vector &f) {
    return (s.x * f.x + s.y * f.y);
}

ld Cross(const Vector &s, const Vector &f) {
    return (s.x * f.y - f.x * s.y);
}

ld GetCross(Point a, Point b, Point c) {
    Vector ba(b, a), bc(b, c);
    return Cross(Vector(b, a), Vector(b, c));
}

ld GetAngle(const Vector &v) {
    return v.GetAngle();
}

ld GetAngle(const Vector &v1, const Vector &v2) {
    return v1.GetAngle(v2);
}

bool PolarAngleComp(const Vector &v1, const Vector &v2) {
    return v1.GetAngle() < v2.GetAngle();
}

bool IsInsideTriangle(const Point &p, const Point &a, const Point &b, const Point &c) {
    Vector pa(p, a), pb(p, b), pc(p, c);
    Vector ab(a, b), ac(a, c);
    ld s1 = abs(Cross(pa, pb)) + abs(Cross(pb, pc)) + abs(Cross(pc, pa));
    ld s2 = abs(Cross(ab, ac));
    return Equal(s1, s2);
}

struct Line {
    ld a, b, c;
    Line() = default;
    Line(const Point &s, const Point &f) {
        a = s.y - f.y;
        b = f.x - s.x;
        c = -a * s.x - b * s.y;
    }
    Line(const Point &s, const Vector &v) {
        Point f(s.x + v.x, s.y + v.y);
        a = s.y - f.y;
        b = f.x - s.x;
        c = -a * s.x - b * s.y;
    }
    Line(ld a, ld b, ld c) : a(a), b(b), c(c) {
    }
    Line(const Segment &seg);
    ld operator()(const Point &other) const {
        return a * other.x + b * other.y + c;
    }
    Point PointByX(ld x = 0) const {
        if (Equal(b, 0)) {
            return kNoIntersection;
        }
        return Point(x, (-c - a * x) / b);
    }
    Point PointByY(ld y = 0) const {
        if (Equal(a, 0)) {
            return kNoIntersection;
        }
        return Point((-c - b * y) / a, y);
    }
    Vector GetPerVec() const {
        return Vector(a, b);
    }
    Vector GetVec() const {
        return Vector(b, -a);
    }
    bool operator<(const Line& other) const {
        return GetAngle(GetVec()) < GetAngle(other.GetVec());
    }
    ld Dist(const Point &p) const {
        return abs(a * p.x + b * p.y + c) / sqrtl(a * a + b * b);
    }
    ld Dist(const Line &l) const {
        Point cur = IntersectWithLine(l);
        if (cur.IsValid()) {
            return 0;
        }
        cur = PointByX();
        if (!cur.IsValid()) {
            cur = PointByY();
        }
        return l.Dist(cur);
    }
    ld Dist(const Segment &seg) const;
    Line Perpendicular(const Point &p) const {
        return Line(p, Vector(a, b));
    }
    Point IntersectWithLine(const Line &l) const;
};

Point IntersectLines(const Line &line1, const Line &line2) {
    Point res;
    ld del = line1.a * line2.b - line1.b * line2.a;
    res.x = -line1.c * line2.b + line2.c * line1.b;
    res.y = -line1.a * line2.c + line2.a * line1.c;
    if (Equal(del, 0)) {
        if (res == kZeroPoint) {
            return kNoIntersection;
        } else {
            return kInfIntersection;
        }
    } else {
        res /= del;
    }
    return res;
}

Point Line::IntersectWithLine(const Line &l) const {
    return IntersectLines(*this, l);
}

struct Segment {
    Point a, b;
    Segment() = default;
    Segment(const Point &a, const Point &b) : a(a), b(b){};
    Segment(const Point &a, const Vector &b) : a(a), b(a + b){};

    ld Len() const {
        return a.Dist(b);
    }
    ld Dist(const Point &p) const {
        ld ans = min(a.Dist(p), b.Dist(p));
        Line l(a, b);
        Point cur = IntersectLines(l, l.Perpendicular(p));
        if (BoundingBox(cur, a, b)) {
            ans = min(ans, cur.Dist(p));
        }
        return ans;
    }
    ld Dist(const Line &l) const {
        Point cur = l.IntersectWithLine(Line(a, b));
        if (BoundingBox(cur, a, b)) {
            return 0;
        }
        return min(l.Dist(a), l.Dist(b));
    }
    ld Dist(const Segment &seg) const {
        Line l1(*this), l2(seg);
        Point cur = IntersectLines(l1, l2);
        if (BoundingBox(cur, a, b) && BoundingBox(cur, seg.a, seg.b)) {
            return 0;
        }
        ld ans = min(seg.Dist(a), seg.Dist(b));
        ans = min(ans, min(Dist(seg.a), Dist(seg.b)));
        return ans;
    }
};

Line::Line(const Segment &seg) : Line(seg.a, seg.b){};

ld Line::Dist(const Segment &seg) const {
    return seg.Dist(*this);
}

ld Point::Dist(const Line &l) const {
    return l.Dist(*this);
}

ld Point::Dist(const Segment &seg) const {
    return seg.Dist(*this);
}

// Polygon must be given in traversal order
ld Dist(const Point &p, const vector<Point> &polygon) {
    if (polygon.empty()) {
        return kInf;
    }
    if (polygon.size() == 1) {
        return p.Dist(polygon[0]);
    }
    if (polygon.size() == 2) {
        return p.Dist(Segment(polygon[0], polygon[1]));
    }
    bool is_inside = false;
    ld ans = kInf;
    Point a = polygon[0];
    for (int i = 1; i < polygon.size() - 1; ++i) {
        Point b = polygon[i];
        Point c = polygon[i + 1];
        if (IsInsideTriangle(p, a, b, c)) {
            is_inside = true;
        }
        ans = min(ans, Segment(b, c).Dist(p));
    }
    if (is_inside) {
        return 0;
    }
    return ans;
}

struct Ray : public Segment {
    Ray() : Segment(){};
    Ray(const Point &f, const Point &s) {
        a = f;
        Vector to(f, s);
        to.Normal();
        to *= kInf;
        b = a + to;
    }
};

struct Circle {
    Point center;
    ld r;
    Circle() = default;
    Circle(const Point &center, ld r) : center(center), r(r) {
    }
    Circle(const Point &a, const Point &b) {
        center = (a + b) / 2;
        r = center.Dist(a);
    }
    Circle(const Point &a, const Point &b, const Point &c) {
        Line ab(a, b), ac(a, c);
        Point median_ab = (a + b) / 2;
        Point median_ac = (a + c) / 2;
        center = IntersectLines(ab.Perpendicular(median_ab), ac.Perpendicular(median_ac));
        r = max(center.Dist(a), center.Dist(b));
    }
    bool Containes(const Point &p) const {
        return center.Dist(p) < r + kEps;
    }
    pair<Point, Point> IntersectWithLine(const Line &l) const;
    pair<Point, Point> IntersectWithCircle(const Line &l) const;
};

pair<Point, Point> IntersectCircleLine(const Circle &c, const Line &l) {
    ld h = l.Dist(c.center);
    if (h > c.r + kEps) {
        return {kNoIntersection, kNoIntersection};
    }
    Vector lv(l.a, l.b);
    Line pl(c.center, lv);
    Point o = IntersectLines(l, pl);
    Vector v1(-l.b, l.a);
    Vector v2 = -v1;
    v1.Normal();
    v2.Normal();
    ld d = sqrtl(c.r * c.r - h * h);
    v1 *= d;
    v2 *= d;
    pair<Point, Point> ans;
    ans.fi = o, ans.se = o;
    ans.fi += v1;
    ans.se += v2;
    return ans;
}

pair<Point, Point> Circle::IntersectWithLine(const Line &l) const {
    return IntersectCircleLine(*this, l);
}

pair<Point, Point> IntersectCircleCircle(const Circle &a, const Circle &b) {
    Line l(2 * (b.center.x - a.center.x), 2 * (b.center.y - a.center.y),
           (a.center.x * a.center.x) - (b.center.x * b.center.x) + (a.center.y * a.center.y) -
               (b.center.y * b.center.y) + (b.r * b.r) - (a.r * a.r));
    return IntersectCircleLine(a, l);
}

pair<Point, Point> GetCircleTangents(Point &p, Circle &c) {
    if (c.center.Dist(p) < c.r + kEps) {
        return {kNoIntersection, kNoIntersection};
    }
    Vector v(p, c.center);
    v *= 0.5;
    Point t = p;
    t += v;
    Circle i(t, v.Len());
    return IntersectCircleCircle(c, i);
    ;
}

// s must sorted and containes pairs of (vector_angle, index in v). Works O(log(v.size()))
pair<Line, Line> GetPolygonTangents(const Line &l, const vector<Point> &v,
                                    const vector<pair<ld, int>> &s) {
    Vector v1(-l.b, l.a);
    Vector v2 = -v1;
    ld a1 = GetAngle(v1), a2 = GetAngle(v2);
    auto it1 = upper_bound(all(s), make_pair(a1, -1));
    auto it2 = upper_bound(all(s), make_pair(a2, -1));
    int k1 = s[0].se;
    int k2 = s[0].se;
    if (it1 != s.end()) {
        k1 = s[it1 - s.begin()].se;
    }
    if (it2 != s.end()) {
        k2 = s[it2 - s.begin()].se;
    }
    Line l1 = Line(v[k1], v1), l2 = Line(v[k2], v2);
    pair<Line, Line> ans = {l1, l2};
    return ans;
}

vector<Point> GetConvex(vector<Point> a) {
    vector<Point> convex;
    if (a.size() == 1) {
        convex.push_back(a[0]);
        return convex;
    }
    sort(a.begin(), a.end());
    Point st = a[0], fi = a[a.size() - 1];
    vector<Point> u, d;
    u.reserve(a.size());
    d.reserve(a.size());
    u.push_back(st);
    d.push_back(st);
    for (int i = 1; i < a.size(); i++) {
        if (i == a.size() - 1 || GetCross(st, a[i], fi) < kEps) {
            while (u.size() >= 2 && GetCross(u[u.size() - 2], u[u.size() - 1], a[i]) > -kEps) {
                u.pop_back();
            }
            u.push_back(a[i]);
        }
        if (i == a.size() - 1 || GetCross(st, a[i], fi) > -kEps) {
            while (d.size() >= 2 && GetCross(d[d.size() - 2], d[d.size() - 1], a[i]) < kEps) {
                d.pop_back();
            }
            d.push_back(a[i]);
        }
    }
    for (int i = 0; i < u.size(); i++) {
        convex.push_back(u[i]);
    }
    for (int i = d.size() - 2; i > 0; i--) {
        convex.push_back(d[i]);
    }
    return convex;
}

pair<Point, Point> NearestPointsRec(vector<Point> &pts, size_t l, size_t r) {
    if (r - l <= 4) {
        pair<Point, Point> ans = {pts[l], pts[r - 1]};
        for (size_t i = l + 1; i < r; ++i) {
            if (DistSqare(ans.fi, ans.se) > DistSqare(pts[i], pts[i - 1])) {
                ans = {pts[i], pts[i - 1]};
            }
        }
        sort(pts.begin() + l, pts.begin() + r, YComp);
        return ans;
    }
    size_t mid = (l + r) / 2;
    ld div = (pts[mid].x + pts[mid - 1].x) / 2;
    auto ans = NearestPointsRec(pts, l, mid);
    ld dist = DistSqare(ans.fi, ans.se);
    auto new_ans = NearestPointsRec(pts, mid, r);
    if (DistSqare(new_ans.fi, new_ans.se) < dist) {
        ans = new_ans;
        dist = DistSqare(new_ans.fi, new_ans.se);
    }
    vector<Point> buf(r - l);
    merge(pts.begin() + l, pts.begin() + mid, pts.begin() + mid, pts.begin() + r, buf.begin(),
          YComp);
    copy(buf.begin(), buf.end(), pts.begin() + l);
    buf.clear();
    for (int i = l; i < r; ++i) {
        if (Sqare(pts[i].x - div) < dist) {
            for (int j = static_cast<int>(buf.size()) - 1; j >= 0; --j) {
                if (Sqare(pts[i].y - buf[j].y) > dist) {
                    break;
                }
                if (DistSqare(pts[i], buf[j]) < dist) {
                    ans = {pts[i], buf[j]};
                    dist = DistSqare(pts[i], buf[j]);
                }
            }
            buf.push_back(pts[i]);
        }
    }
    return ans;
}

pair<Point, Point> FindNearestPoints(vector<Point> pts) {
    if (pts.size() <= 1) {
        return {kNoIntersection, kNoIntersection};
    }
    if (pts.size() == 2) {
        return {pts[0], pts[1]};
    }
    sort(all(pts));
    return NearestPointsRec(pts, 0, pts.size());
}

// Polygons must be given in traversal order
vector<Point> MinkowskiAddition(const vector<Point> &polygon1, const vector<Point> &polygon2) {
    vector<Vector> vecs;
    vecs.reserve(polygon1.size() + polygon2.size());
    auto cmp = [](const Point &a, const Point &b) {
        return a.y < b.y || (Equal(a.y, b.y) && a.x < b.x);
    };
    Point start_a(kInf, kInf);
    for (int i = 0; i < polygon1.size(); ++i) {
        vecs.emplace_back(polygon1[i], polygon1[(i + 1) % polygon1.size()]);
        if (cmp(polygon1[i], start_a)) {
            start_a = polygon1[i];
        }
    }
    Point start_b(kInf, kInf);
    for (int i = 0; i < polygon2.size(); ++i) {
        vecs.emplace_back(polygon2[i], polygon2[(i + 1) % polygon2.size()]);
        if (cmp(polygon2[i], start_b)) {
            start_b = polygon2[i];
        }
    }
    vector<Point> ans;
    ans.reserve(polygon1.size() + polygon2.size());
    sort(all(vecs), PolarAngleComp);
    auto cur = start_a + start_b;
    ans.push_back(cur);
    for (const auto &v : vecs) {
        cur += v;
        ans.push_back(cur);
    }
    return ans;
}

vector<Point> Negative(const vector<Point> &a) {
    vector<Point> ans(a.size());
    for (int i = 0; i < ans.size(); ++i) {
        ans[i] = -a[i];
    }
    return ans;
}

Circle GetMinCoveringCircle(vector<Point> pts) {
    shuffle(pts.begin(), pts.end(), rnd);
    if (pts.size() == 1) {
        return Circle(pts[0], 0);
    }
    Circle ans(pts[0], pts[1]);
    for (int k = 2; k < pts.size(); ++k) {
        if (ans.Containes(pts[k])) {
            continue;
        }
        shuffle(pts.begin(), pts.begin() + k, rnd);
        Circle ans1(pts[k], pts[0]);
        for (int i = 1; i < k; ++i) {
            if (ans1.Containes(pts[i])) {
                continue;
            }
            Circle ans2(pts[k], pts[i]);
            for (int j = 0; j < i; ++j) {
                if (ans2.Containes(pts[j])) {
                    continue;
                }
                ans2 = Circle(pts[k], pts[i], pts[j]);
            }
            ans1 = ans2;
        }
        ans = ans1;
    }
    return ans;
}

int main() {
    ios_base::sync_with_stdio(0);
    cin.tie(nullptr);
    cout.tie(nullptr);
    cout << fixed << setprecision(10);

    return 0;
}
