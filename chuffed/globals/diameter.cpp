//#include <stdio.h>
#include <iostream>
#include <chuffed/core/propagator.h>

#include <float.h>

class Diameter : public Propagator, public Checker {
    vec<int> dist;
    vec<IntVar*> x;
    IntVar* y;
  	// Intermediate state
  	vec<int> new_fixed;
    bool ub_changed;
public:
    Diameter(vec<IntVar*>& x0, vec<int>& dist0, IntVar* y0)
    : dist(dist0), x(x0), y(y0), ub_changed(false) {
      new_fixed.reserve(x.size());
      for (int i = 0; i < x.size(); i++) {
        x[i]->attach(this, i, EVENT_F);
      }
      y->attach(this, x.size(), EVENT_U);
    }
    
    int dd(int i, int j) {
      return dist[i*x.size()+j];
    }
    
    void wakeup(int i, int c) {
      if (i<x.size()) {
        assert(x[i]->isFixed());
        new_fixed.push(i);
      } else {
        ub_changed = true;
      }
      pushInQueue();
    }
    
    bool propagate() {
      if (ub_changed) {
        new_fixed.clear();
        for (unsigned int i=0; i<x.size(); i++)
          if (x[i]->isFixed())
            new_fixed.push(i);
      }
      
      for (int i=new_fixed.size(); i--; ) {
        int j = new_fixed[i];
        
        for (int k=0; k<x.size(); k++) {
          int dist_j_k = dd(j,k);
          if (dist_j_k >= y->getMax()) {
            setDom((*x[k]), remVal, x[j]->getVal(), x[j]->getValLit(), y->getMaxLit());
          }
          if (x[k]->isFixed() && x[k]->getVal() == x[j]->getVal()) {
            setDom((*y), setMin, dist_j_k, x[j]->getValLit(), x[k]->getValLit());
          }
          
        }
      }
      return true;
    }
    
    void clearPropState() {
      in_queue = false;
      ub_changed = false;
      new_fixed.clear();
    }
    
    bool check() {
      for (int i=0; i<x.size(); i++) {
        for (int j=0; j<x.size(); j++) {
          if (x[i]->getShadowVal()==x[j]->getShadowVal() && dd(i,j) > y->getShadowVal())
            return false;
        }
      }
      return true;
    }
    
};

void diameter(vec<IntVar*>& x, vec<int>& dist, IntVar* y) {
  new Diameter(x,dist,y);
}

class ClusterDistanceSum : public Propagator, public Checker {
    vec<int> dist;
    vec<IntVar*> x;
    IntVar* y;
    int c;
    
    vec<int> all_fixed;
    
  	// Intermediate state
  	vec<int> new_fixed;
    bool ub_changed;
    
    Tint num_fixed;
    Tint num_others;
    
    Tint64_t sum_of_fixed;
public:
    ClusterDistanceSum(vec<IntVar*>& x0, vec<int>& dist0, int c0, IntVar* y0)
    : dist(dist0), x(x0), y(y0), c(c0), all_fixed(x0.size()), ub_changed(false) {
      num_fixed = 0;
      num_others = 0;
      sum_of_fixed = 0;
      new_fixed.reserve(x.size());
      for (int i = 0; i < x.size(); i++) {
        x[i]->attach(this, i, EVENT_F);
      }
      y->attach(this, x.size(), EVENT_U);
    }
    
    int64_t dd(int i, int j) {
      return dist[i*x.size()+j];
    }
    
    void wakeup(int i, int cause) {
      if (i<x.size()) {
        assert(x[i]->isFixed());
        if (x[i]->getVal()==c) {
          new_fixed.push(i);
          pushInQueue();
        } else {
          num_others++;
          if (num_fixed+num_others==x.size())
            pushInQueue();
        }
      } else {
        ub_changed = true;
        pushInQueue();
      }
    }
    
    bool propagate() {
      // std::cerr << "prop "<< num_fixed << " " << new_fixed.size() << " " << num_others << " " << sum_of_fixed;
      for (int i=new_fixed.size(); i--; ) {
        all_fixed[num_fixed+i] = new_fixed[i];
      }

      for (int i=num_fixed; i<num_fixed+new_fixed.size(); i++) {
        for (int j=0; j<i; j++) {
          sum_of_fixed += dd(all_fixed[i], all_fixed[j])*dd(all_fixed[i], all_fixed[j]);
        }
      }

      num_fixed += new_fixed.size();
      
      // std::cerr << "  " << sum_of_fixed << "\n";
      
      int sum_of_fixed_scaled_lb = std::floor(sum_of_fixed / 10000.0);
      int sum_of_fixed_scaled_ub = std::ceil(sum_of_fixed / 10000.0);
      
      if (y->setMinNotR(sum_of_fixed_scaled_lb)) {
        vec<Lit> ps(num_fixed);
        Reason expl;
        if (so.lazy) {
          for (int i=0; i<num_fixed; i++) {
            ps[i] = x[all_fixed[i]]->getValLit();
          }
          expl = Reason_new(ps);
        }
        if (!y->setMin(sum_of_fixed_scaled_lb, expl)) {
          return false;
        }
      }
                  
      if (num_fixed+num_others==x.size() && y->setMaxNotR(sum_of_fixed_scaled_ub)) {
        vec<Lit> ps(x.size());
        Reason expl;
        if (so.lazy) {
          for (int i=0; i<x.size(); i++) {
            ps[i] = x[i]->getValLit();
          }
          expl = Reason_new(ps);
        }
        if (!y->setMax(sum_of_fixed_scaled_ub, expl)) {
          return false;
        }
      }

      return true;
    }
    
    void clearPropState() {
      in_queue = false;
      ub_changed = false;
      new_fixed.clear();
    }
    
    bool check() {
      int sum_of_vals = 0;
      for (int i=0; i<x.size(); i++) {
        for (int j=0; j<i; j++) {
          if (x[i]->getShadowVal()==c && x[j]->getShadowVal()==c)
            sum_of_vals += dd(i,j);
        }
      }
      return sum_of_vals == y->getShadowVal();
    }
    
};


void cluster_distance_sum(vec<IntVar*>& x, vec<int>& dist, int c, IntVar* y) {
  new ClusterDistanceSum(x,dist,c,y);
}

class WCSS : public Propagator {
  vec<int> dist;
  vec<IntVar*> x;
  IntVar* y;
  int k;
  
  const double scale = 100000.0;

  vec<vec<double> > borne;
  vec<vec<int> > setP; 	// set of fixed points
  vec<int> setQ;	// set of non-fixed points
  vec<double> sizeCluster; // number of point in a cluster
  vec<double> V1; // V1[c] = V1 of cluster Cc

public:
  WCSS(vec<IntVar*>& x0, vec<int>& dist0, IntVar* y0, int k0)
  : dist(dist0), x(x0), y(y0), k(k0), borne(k0), setP(k), sizeCluster(k), V1(k) {
    for (int i = 0; i < x.size(); i++) {
      x[i]->attach(this, i, EVENT_F);
    }
    y->attach(this, x.size(), EVENT_U);
    setQ.reserve(x.size());
    for (int i=0; i<k; i++)
      setP[i].reserve(x.size());
  }
  
  double dd(int i, int j) {
    return static_cast<double>(dist[i*x.size()+j]);
  }
  
  void calcBorne(int q, vec<vec<double> >& v2, vec<vec<double> >& dQQ, vec<double>& V1,
                 vec<double>& sizeCluster, vec<vec<double> >& borne) {
    // calculation of Table borne[k][q+1]
    for (int c = 0; c < k; c++)
      for (int m = 0; m <= q; m++) { // borne if we add m points to cluster Cc
        vec<double> v23(q); // v23 of each points
        
        for (int i = 0; i < q; i++)
          if (m > 1)
            v23[i] = ( v2[i][c] + dQQ[i][m-1] );
          else
            v23[i] = ( v2[i][c] );
        
        std::sort ((double*)v23, (double*)v23 + v23.size());
        
        double v123 = V1[c];
        for (int  i = 0; i < m; i++)
          v123 += v23[i];
        
        if (m + sizeCluster[c] > 0)
          borne[c][m] = v123 / (m + sizeCluster[c]);
        else
          borne[c][m] = 0;
      }
    
  }
  
  bool propagate() {
    
    int n = x.size();
    int q = 0; // number of unassigned point;
    int p = 0; // number of fixed point;
    
    for (int i=0; i<k; i++)
      setP[i].clear();
    setQ.clear();
    
    vec<Lit> ps;
    
    // get the set of assigned and unassigned points
    for (int i = 0; i < n; i++)
      if (x[i]->isFixed()) {
        p++;
        setP[x[i]->getVal()-1].push(i);
        ps.push(x[i]->getValLit());
//        std::cerr << "push " << i << " " << (sat.value(x[i]->getValLit())==l_False) << "\n";
      }
      else  {
        q++;
        setQ.push(i);
        for (int c=0; c<k; c++) {
          if (!x[i]->indomain(c+1)) {
            ps.push(x[i]->getLit(c+1, 1)); // push x[i] != c literal
//            std::cerr << "push " << i << " " << (c+1) << " " << (sat.value(x[i]->getLit(c+1,0))==l_Undef) << "\n";
          }
        }
      }
    
//    std::cerr << "prop " << p << "," << q << ":";

//    if (q >= x.size() / 3) {
////      std::cerr << "!\n";
//      return true;
//    }

    // get the size of each cluster
    for (int c = 0; c < k; c++)
      sizeCluster[c] = setP[c].size();
    
    
    // declaration of borne[k][q+1], borne[c][m]: minimum wcss of cluster Cc if we have m points
    for (int c = 0; c < k; c++) {
      borne[c].growTo(q+1);
      for (int m = 0; m <= q; m++)
        borne[c][m] = 0;
    }
    
    // calculatation of V1 of each cluster
    for (int c = 0; c < k; c++) {
      V1[c] = 0;
      for (int i = 0; i < setP[c].size(); i++)
        for (int j = i+1; j < setP[c].size(); j++) {
          V1[c] += dd( setP[c][i] , setP[c][j] ) * dd( setP[c][i] , setP[c][j] ) ;
        }
      
    }
    
//    std::cerr << "1";
    
    // Calculation of distance from each non fix point to each cluster Cc
    vec<vec<double> > v2(q); // v2[i][c] = sum of distance from i to every points in cluster Cc. V2[i][c] = max if c is not in the domain of i
    for (int i = 0; i < q; i++) {
      v2[i].growTo(k);
      for (int c = 0; c < k; c++) 	{
        // now check every points in cluster Cc
        if (x[ setQ[i] ]->indomain(c+1)) {
          v2[i][c] = 0;
          for (int j = 0; j < setP[c].size(); j++)
            v2[i][c] += dd( setQ[i] , setP[c][j] ) * dd( setQ[i] , setP[c][j] );
        }
        else
          v2[i][c] = 10000000000000;
      }
    }

//    std::cerr << "2";

    // Calculation of distance between non fix points
    
    // dQQ: distance between non assigned points
    vec<vec<double> > dQQ(q);  // dQQ[i][j] = sum of distance from j-1 points to i. We know that dQQ[i] has q elements
    for (int i = 0; i < setQ.size(); i++)
      for (int j = 0; j < setQ.size(); j++)
        dQQ[i].push( dd( setQ[i] , setQ[j] ) * dd( setQ[i] , setQ[j] )/2);
    
    for (int i = 0; i < q; i++)
      std::sort ((double*)dQQ[i], (double*)dQQ[i] + dQQ[i].size());
    
    
    for (int i = 0; i < q; i++)
      for (int j = 1; j < q; j++)
        dQQ[i][j] += dQQ[i][j-1];
    
//    std::cerr << "3";

    calcBorne(q, v2, dQQ, V1, sizeCluster, borne);

//    std::cerr << "4";

    // calculation of k-1 column borneMulti[k][q+1]: borneMulti[c][m] = C1+C2+...+Cc if we add m points
    vec<vec<double> > borneMulti(k); // [k][q+1];
    for (int c = 0; c < k; c++)	{
      borneMulti[c].growTo(q+1);
    }
    for (int i = 0; i <= q; i++)
      borneMulti[0][i] = borne[0][i]; // first column is the same
    
    for (int c = 1; c < k; c++)	{
      for (int m = 0; m <= q; m++) {
        borneMulti[c][m] = 10000000000000;
        for (int i = 0; i <= m; i++) { // if we get i points from cluster Cc and m-i points from previous clusters C1,C2,..,Cc-1
          if (borneMulti[c][m] > (borne[c][i] + borneMulti[c-1][m-i]) )					
            borneMulti[c][m] = borne[c][i] + borneMulti[c-1][m-i];				
        }
      }			
    }

//    std::cerr << "5";
    
//    if (q==0) {
//      double wcss = 0.0;
//      for (int c=0; c<k; c++) {
//        wcss += V1[c] / (sizeCluster[c]);
//      }
//      std::cerr << "got " << wcss << " vs " << borneMulti[k-1][q] << "\n";
//    }
    
    double newLB = borneMulti[k-1][q];
    
    int newLB_lb = std::floor(newLB / scale);
    int newLB_ub = std::ceil(newLB / scale);
    
    if (y->setMinNotR(newLB_lb)) {
      Reason expl;
      if (so.lazy) {
        expl = Reason_new(ps);
      }
      if (!y->setMin(newLB_lb, expl)) {
//        std::cerr << "!1\n";
        return false;
      }
    }
    
    if (q==0) {
      if (y->setMaxNotR(newLB_ub)) {
        Reason expl;
        if (so.lazy) {
          expl = Reason_new(ps);
        }
        if (!y->setMax(newLB_ub, expl)) {
//          std::cerr << "!2\n";
          return false;
        }
      }
      return true;
    }

    for (int c = 0; c < k; c++) {	// we filter value c in each points
      
      // First, build the column borneExcept[0..q]: borneExcept[m] = borne if we add m points to cluster C1->Ck except cluster Cc
      vec<double> borneExcept(q);
      for (int i = 0; i < q; i++) {	// i from 0 to q-1
        borneExcept[i] = 0;
        for (int j = i; j <= q; j++)
          if (borneExcept[i] < (borneMulti[k-1][j] - borne[c][j-i]))	// k-1 is the last columnm
            borneExcept[i] = borneMulti[k-1][j] - borne[c][j-i];
      }
      
      
      
      
      //for (int i = 0; i < q; i++)
      //	cout << borneExcept[i] - bound[i][0] << " ";    Why boundEcept is better
      
      
      // Filtering points
      for (int i = 0; i < q; i++)
        if (x[ setQ[i] ]->indomain(c+1))  {	// if c is in the domain of points x[ setQ[i] ]
          // calculation bound if we add point setQ[i] and others m points
          
          vec<double> borneM(q+1); // borne[m+1] if we add point i and other m points to cluster Cc
          for (int m = 0; m < q; m++) { // m from 0 to q-1
            double xx = borne[c][m] * (sizeCluster[c] + m) + v2[i][c] + 2 * dQQ[i][m];
            double yy = sizeCluster[c] + m + 1; // size of cluster if we add point i and m points
            borneM[m+1] = xx/yy;
          }
          
          double minBorne = 10000000000000; // borne if we add Total q point = point i + m point to Cc + q-m points to others
          for (int m = 0; m < q; m++)
            if (minBorne > (borneM[1+m] + borneExcept[q-m-1]))
              minBorne = borneM[1+m] + borneExcept[q-m-1];
          
          if (ceil(minBorne / scale) >= y->getMax()) {

            if (x[ setQ[i] ]->remValNotR(c+1)) {
              Reason expl;
              if (so.lazy) {
                ps.clear();

                for (int j = 0; j < n; j++) {
                  if (j == setQ[i])
                    continue;
                  if (x[j]->isFixed()) {
                    ps.push(x[j]->getValLit());
                  }
                  else  {
                    for (int c=0; c<k; c++) {
                      if (!x[j]->indomain(c+1))
                        ps.push(x[j]->getLit(c+1, 1)); // push x[j] != c literal
                    }
                  }
                }
                ps.push(y->getMaxLit());
                expl = Reason_new(ps);
              }
              if (!x[ setQ[i] ]->remVal(c+1, expl)) {
//                std::cerr << "!3\n";
                return false;
              }
            }

            
          }
//            GECODE_ME_CHECK(x[ setQ[i] ].nq(home, c));
          
          
        }
      
      
      
    }
    
//    std::cerr << "6\n";
    
    return true;
  }
  
};


void wcss(vec<IntVar*>& x, vec<int>& dist, IntVar* y, int k) {
  new WCSS(x,dist,y,k);
}

int pivot(double* a, int* pX, int* pY, int first, int last) {
  int  p = first;
  double pivotElement = a[first];
  
  for(int i = first+1 ; i <= last ; i++) {
    if(a[i] <= pivotElement) {
      p++;
      std::swap(a[i], a[p]);
      std::swap(pX[i], pX[p]);
      std::swap(pY[i], pY[p]);
    }
  }
  
  std::swap(a[p], a[first]);
  std::swap(pX[p], pX[first]);
  std::swap(pY[p], pY[first]);
  
  return p;
}

inline void quickSort( double* a, int* pX, int* pY, int first, int last ) {
  int pivotIndex;
  
  if(first < last) {
    pivotIndex = pivot(a, pX, pY, first, last);
    quickSort(a, pX, pY, first, pivotIndex-1);
    quickSort(a, pX, pY, pivotIndex+1, last);
  }
}

double dd(const vec<int>& dist, int n, int i, int j) {
  return static_cast<double>(dist[i*n+j])*static_cast<double>(dist[i*n+j]);
}

void sortDistances(const vec<int>& dist, int n, double* dSort, int* pX, int* pY) {
  int count = 0;
  for (int i = 0; i < n; i++)
    for (int j = i+1; j <n; j++) {
      pX[count] = i;
      pY[count] = j;
      count++;
    }
  
  count = 0;
  for (int i = 0; i < n; i++)
    for (int j = i+1; j <n; j++) {
      dSort[count] = dd(dist,n,i,j); // dd[i][j] * dd[i][j];
      count++;
    }
  
  quickSort(dSort, pX, pY, 0, count-1);
}


class WCSD : public Propagator {
  vec<int> dist;
  vec<IntVar*> x;
  IntVar* y;
  int k;
  
  const double scale = 100000.0;

  vec<int> pX;
  vec<int> pY;
  vec<double> dSort;

  vec< vec<double> > add;
  vec<double> minContrib;
  vec<int> assigned;

  vec< vec<double> > _add;
  vec<double> _minContrib;

public:
  double dd(int i, int j) {
    return static_cast<double>(dist[i*x.size()+j])*static_cast<double>(dist[i*x.size()+j]);
  }
  
  WCSD(vec<IntVar*>& x0, vec<int>& dist0, IntVar* y0, int k0)
  : dist(dist0), x(x0), y(y0), k(k0),
    add(x0.size()), minContrib(x0.size()),
    _add(x0.size()), _minContrib(x0.size()) {
    for (int i = 0; i < x.size(); i++) {
      x[i]->attach(this, i, EVENT_F);
    }
    y->attach(this, x.size(), EVENT_U);
    
    int n = x.size();
    pX.growTo(n*(n-1)/2);
    pY.growTo(n*(n-1)/2);
    dSort.growTo(n*(n-1)/2);

    for (int i=0; i<x.size(); i++) {
      add[i].growTo(k);
      _add[i].growTo(k);
    }

    assigned.reserve(x0.size());
    
    sortDistances(dist, x.size(), &dSort[0], &pX[0], &pY[0]);
  }
  
  void compute(double& V1, double& V2, double& V3, double& V4, int& nAssign, int ignore=-1) {
    int n=x.size();

    vec<vec<double> >& myAdd = ignore==-1 ? add : _add;
    vec<double>& myMinContrib = ignore==-1 ? minContrib : _minContrib;
    
    if (ignore==-1)
      assigned.clear();
    
    nAssign=0;
    for (int i = 0; i < n; i++) {
      if (x[i]->isFixed() && i!=ignore) {
        nAssign++;
        if (ignore==-1)
          assigned.push(i);
      }
    }
    
    V1 = V2 = V3 = V4 = 0.0;

    // restrict to cases where k is the number of clusters
    // ie. any value c<k must be in at least one domain of G_i
    
    // vector<int> checkClass(k,0); // checkClass[c]=1 iff class c exists in one domain of G_i?
    // // it may exist a number c<k that is in no domain
    
    // int countCheck  = 0;
    // for (int i = 0; i < n; i++) {
    //   for  (Int::ViewValues<Int::IntView> z(x[i]); z(); ++z)  // back up value of variable x[i]
    //     if (checkClass[z.val()] == 0) {
    // 	countCheck++;
    // 	checkClass[z.val()] = 1;
    //     }
    //   if (countCheck == k) break;
    // }
    // // what if countCheck < k???
    
    for (int i = 0; i < myAdd.size(); i++) {
      myMinContrib[i] = DBL_MAX;
      for (int j=0; j<k; j++)
        myAdd[i][j] = dd(i,i);
    }
    
    // compute add array
    // add[i][c] added amount if point i is assigned to cluster c
    // when point i is really assigned to cluster c, add[i][c] is the amount relating to i
    // NEED TO CONSIDER WHEN ML-BLOCKS!!!
    for (int i = 0; i < n; i++)
      for (int j = i+1; j< n; j++)
        if (x[i]->isFixed() && i != ignore) {
          if (x[j]->isFixed() && j != ignore && x[i]->getVal()==x[j]->getVal()) {
            myAdd[i][x[i]->getVal()-1] += dd(i,j);
            myAdd[j][x[j]->getVal()-1] += dd(i,j);
          } else if (!x[j]->isFixed() && (j==ignore || x[j]->indomain(x[i]->getVal()))) {
            myAdd[j][x[i]->getVal()-1] += dd(i,j);
          }
        } else { // x[i] not assigned
          if (x[j]->isFixed() && (i==ignore || x[i]->indomain(x[j]->getVal())))
            myAdd[i][x[j]->getVal()-1] += dd(i,j);
        }
    
    // compute minContrib for unassigned variables
    V2 = 0;
    for (int i=0; i<n; i++)
      if (!x[i]->isFixed() || i==ignore) {
        for (int c=0; c<k; c++)
          if ((i == ignore || x[i]->indomain(c+1)) && myMinContrib[i]>myAdd[i][c])
            myMinContrib[i] = myAdd[i][c];
        V2 += myMinContrib[i];
      }
    
    // compute V1
    V1 = 0;
    for (int i=0; i<n; i++)
      if (x[i]->isFixed() && i != ignore)
        V1 += myAdd[i][x[i]->getVal()-1];
    V1 = V1/2; // since each distance is counted twice
    
    // compute nConnexions = f(p,k) and nConnRev = f(p-1,k)
    int nUnassign = n-nAssign;
    int mSize = nUnassign/k;
    int remainder = nUnassign % k;
    int nConnexions = (k*mSize*mSize + 2*mSize*remainder - k*mSize)/2;
    mSize = (nUnassign-1) / k;
    remainder = (nUnassign-1) % k;
    int nConnRev = (k*mSize*mSize + 2*mSize*remainder - k*mSize)/2;
    
    // compute V3 and V4
    V3 = 0;
    V4 = 0;
    int count = 0;
    
    for (int pos = 0; pos < (n * (n-1)/2); pos++)  {
      //if (count >= nPair + nPair - nPair2) break;
      if (count >= nConnexions)
        break;
      int i = pX[pos];
      int j = pY[pos];
      if ((!x[i]->isFixed() || i==ignore) && (!x[j]->isFixed() || j==ignore)) {
        int checkSameDomain = 0;
        for (int c = 0; c < k; c++)
          if (  (i==ignore || x[i]->indomain(c+1)) && (j==ignore || x[j]->indomain(c+1))) {
            checkSameDomain = 1;
            break;
          }
        if (checkSameDomain) { // two points i and j can be in the same cluster
          if (count < nConnexions)
            V3 += dSort[pos];
          if (count < nConnRev) {
            V4 += dSort[pos];
          }
          count++;
        }
      }
    }
  }
  
  bool propagate() {

    int n = x.size();
    int nAssign;
    double V1, V2, V3, V4;
    
    compute(V1, V2, V3, V4, nAssign);

    int nUnassign = n-nAssign;
    
    double inf = V1 + V2 + V3;
    
    if (inf / scale > IntVar::max_limit)
      std::cerr << "OVERFLOW\n";
    
    int newLB_lb = std::floor(inf / scale);
    int newLB_ub = std::ceil(inf / scale);
    
    vec<Lit> ps;

    if (so.lazy && (y->setMinNotR(newLB_lb) || (nUnassign==0 && y->setMaxNotR(newLB_ub)))) {
      for (int i = 0; i < n; i++) {
        if (x[i]->isFixed()) {
          ps.push(x[i]->getValLit());
        }
        else  {
          for (int c=0; c<k; c++) {
            if (!x[i]->indomain(c+1)) {
              ps.push(x[i]->getLit(c+1, 1)); // push x[i] != c literal
            }
          }
        }
      }
    }
    
    if (y->setMinNotR(newLB_lb)) {
      Reason expl;
      if (so.lazy) {
        expl = Reason_new(ps);
      }
      if (!y->setMin(newLB_lb, expl)) {
        //        std::cerr << "!1\n";
        return false;
      }
    }
    
    if (nUnassign==0) {
      if (y->setMaxNotR(newLB_ub)) {
        Reason expl;
        if (so.lazy) {
          expl = Reason_new(ps);
        }
        if (!y->setMax(newLB_ub, expl)) {
          //          std::cerr << "!2\n";
          return false;
        }
      }
      return true;
    }
    
    
    for (int i = 0; i < n; i++) 
      if (!x[i]->isFixed()) {
        //double delta = V4 - contribute[i] + addDelta[i];
        for (int c=0; c<k; c++) {
          if (x[i]->indomain(c+1)) {
            if ( (V1 + V2 + V4 + add[i][c] - minContrib[i]) / scale > y->getMax()) {

              if (x[i]->remValNotR(c+1)) {
                Reason expl;
                if (so.lazy) {
                  
                  int ignore = -1;
//                  for (int ia=assigned.size(); ia--;) {
//                    double _V1, _V2, _V3, _V4;
//                    int _nAssign;
//                    compute(_V1, _V2, _V3, _V4, _nAssign, assigned[ia]);
//                    if ( (_V1 + _V2 + _V4 + _add[i][c] - _minContrib[i]) / scale > y->getMax()) {
//                      ignore = assigned[ia];
////                      break;
//                    }
//                  }
                  
                  ps.clear();
                  
                  for (int j = 0; j < n; j++) {
                    if (j == i || j==ignore)
                      continue;
                    if (x[j]->isFixed()) {
                      ps.push(x[j]->getValLit());
                    }
                    else  {
                      for (int c=0; c<k; c++) {
                        if (!x[j]->indomain(c+1))
                          ps.push(x[j]->getLit(c+1, 1)); // push x[j] != c literal
                      }
                    }
                  }
                  ps.push(y->getMaxLit());
                  expl = Reason_new(ps);
                }
                if (!x[i]->remVal(c+1, expl)) {
                  //                std::cerr << "!3\n";
                  return false;
                }
              }
              
              
            }
          }
        }
      }
    
    return true;
  }
  
//  Clause* explain(Lit p, int inf_id) {
//    
//  }
  
};


void wcsd(vec<IntVar*>& x, vec<int>& dist, IntVar* y, int k) {
  new WCSD(x,dist,y,k);
}
