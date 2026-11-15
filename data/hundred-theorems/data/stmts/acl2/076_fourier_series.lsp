;; Statement-only formalization of hundred-theorems corpus artifact
;; hundred-theorems__acl2__076, "Fourier Series": the Fourier partial sums of
;; every square-integrable real function on [-pi,pi] converge to that function
;; in the L2 norm. This file contains no proof.
;; Manual semantic audit (2026-09-06): retained as a historical candidate,
;; but not counted as a faithful standard-ACL2 translation. See
;; corpus-extension/semantic_canonical_resolutions.json for the blocker.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no primitive real or Hilbert-space sorts.  The arguments of the
;; final predicate therefore give an exact presentation of the complete
;; ordered field of reals and of the real L2 Hilbert space.  The normalized
;; trigonometric system is represented, up to its basis-preserving isometric
;; identification with L2[-pi,pi], by a countable orthonormal basis with dense
;; finite span.  APPLY$ function objects retain the arbitrary carriers,
;; functions, sequences, and subsets; none is replaced by a finite table.

(defun fs076-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun fs076-binary (operation x y)
  (apply$ operation (list x y)))

(defun fs076-positive-p (carrier less zero x)
  (and (fs076-member-p carrier x)
       (apply$ less (list zero x))))

(defun-sk fs076-field-laws-p
    (carrier add multiply negate inverse zero one less)
  (forall (x y z)
    (implies
     (and (fs076-member-p carrier x)
          (fs076-member-p carrier y)
          (fs076-member-p carrier z))
     (and
      (fs076-member-p carrier
                      (fs076-binary add x y))
      (fs076-member-p carrier
                      (fs076-binary multiply x y))
      (fs076-member-p carrier
                      (apply$ negate (list x)))
      (implies
       (not (equal x zero))
       (fs076-member-p carrier
                       (apply$ inverse (list x))))
      (equal
       (fs076-binary add (fs076-binary add x y) z)
       (fs076-binary add x (fs076-binary add y z)))
      (equal (fs076-binary add x y)
             (fs076-binary add y x))
      (equal (fs076-binary add x zero) x)
      (equal (fs076-binary add x (apply$ negate (list x)))
             zero)
      (equal
       (fs076-binary multiply
                     (fs076-binary multiply x y) z)
       (fs076-binary multiply
                     x (fs076-binary multiply y z)))
      (equal (fs076-binary multiply x y)
             (fs076-binary multiply y x))
      (equal (fs076-binary multiply x one) x)
      (implies
       (not (equal x zero))
       (equal
        (fs076-binary multiply
                      x (apply$ inverse (list x)))
        one))
      (equal
       (fs076-binary multiply
                     x (fs076-binary add y z))
       (fs076-binary add
                     (fs076-binary multiply x y)
                     (fs076-binary multiply x z)))))))

(defun-sk fs076-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and (fs076-member-p carrier x)
          (fs076-member-p carrier y)
          (fs076-member-p carrier z))
     (and
      (not (apply$ less (list x x)))
      (or (equal x y)
          (apply$ less (list x y))
          (apply$ less (list y x)))
      (implies
       (and (apply$ less (list x y))
            (apply$ less (list y z)))
       (apply$ less (list x z)))
      (implies
       (apply$ less (list x y))
       (apply$ less
               (list (fs076-binary add x z)
                     (fs076-binary add y z))))
      (implies
       (and (apply$ less (list zero x))
            (apply$ less (list zero y)))
       (apply$ less
               (list zero
                     (fs076-binary multiply x y))))))))

(defun-sk fs076-set-nonempty-p (carrier set)
  (exists (x)
    (and (fs076-member-p carrier x)
         (apply$ set (list x)))))

(defun-sk fs076-upper-bound-p (carrier less set bound)
  (forall (x)
    (implies
     (and (fs076-member-p carrier x)
          (apply$ set (list x)))
     (not (apply$ less (list bound x))))))

(defun-sk fs076-bounded-above-p (carrier less set)
  (exists (bound)
    (and (fs076-member-p carrier bound)
         (fs076-upper-bound-p
          carrier less set bound))))

(defun-sk fs076-supremum-p (carrier less set supremum)
  (forall (bound)
    (and
     (fs076-member-p carrier supremum)
     (fs076-upper-bound-p
      carrier less set supremum)
     (implies
      (and (fs076-member-p carrier bound)
           (fs076-upper-bound-p
            carrier less set bound))
      (not (apply$ less
                   (list bound supremum)))))))

(defun-sk fs076-has-supremum-p (carrier less set)
  (exists (supremum)
    (fs076-supremum-p
     carrier less set supremum)))

(defun-sk fs076-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and (tamep-functionp set)
          (fs076-set-nonempty-p carrier set)
          (fs076-bounded-above-p carrier less set))
     (fs076-has-supremum-p
      carrier less set))))

(defun fs076-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (fs076-member-p carrier zero)
   (fs076-member-p carrier one)
   (not (equal zero one))
   (fs076-field-laws-p
    carrier add multiply negate inverse zero one less)
   (fs076-order-laws-p
    carrier add multiply zero less)
   (apply$ less (list zero one))
   (fs076-dedekind-complete-p carrier less)))

(defun fs076-vector-difference (add negate x y)
  (fs076-binary add x (apply$ negate (list y))))

(defun-sk fs076-vector-space-laws-p
    (scalar-carrier scalar-add scalar-multiply scalar-one
     carrier add negate zero smul)
  (forall (a b x y z)
    (implies
     (and (fs076-member-p scalar-carrier a)
          (fs076-member-p scalar-carrier b)
          (fs076-member-p carrier x)
          (fs076-member-p carrier y)
          (fs076-member-p carrier z))
     (and
      (fs076-member-p carrier (fs076-binary add x y))
      (fs076-member-p carrier (apply$ negate (list x)))
      (fs076-member-p carrier (fs076-binary smul a x))
      (equal
       (fs076-binary add (fs076-binary add x y) z)
       (fs076-binary add x (fs076-binary add y z)))
      (equal (fs076-binary add x y)
             (fs076-binary add y x))
      (equal (fs076-binary add x zero) x)
      (equal (fs076-binary add x (apply$ negate (list x)))
             zero)
      (equal (fs076-binary smul scalar-one x) x)
      (equal
       (fs076-binary smul
                     (fs076-binary scalar-multiply a b) x)
       (fs076-binary smul
                     a (fs076-binary smul b x)))
      (equal
       (fs076-binary smul
                     (fs076-binary scalar-add a b) x)
       (fs076-binary add
                     (fs076-binary smul a x)
                     (fs076-binary smul b x)))
      (equal
       (fs076-binary smul a (fs076-binary add x y))
       (fs076-binary add
                     (fs076-binary smul a x)
                     (fs076-binary smul a y)))))))

(defun-sk fs076-inner-product-laws-p
    (scalar-carrier scalar-add scalar-multiply scalar-zero less
     carrier add zero smul inner)
  (forall (a x y z)
    (implies
     (and (fs076-member-p scalar-carrier a)
          (fs076-member-p carrier x)
          (fs076-member-p carrier y)
          (fs076-member-p carrier z))
     (and
      (fs076-member-p scalar-carrier
                      (fs076-binary inner x y))
      (equal
       (fs076-binary inner x (fs076-binary add y z))
       (fs076-binary scalar-add
                     (fs076-binary inner x y)
                     (fs076-binary inner x z)))
      (equal
       (fs076-binary inner x (fs076-binary smul a y))
       (fs076-binary scalar-multiply
                     a (fs076-binary inner x y)))
      (equal (fs076-binary inner x y)
             (fs076-binary inner y x))
      (not
       (apply$ less
               (list (fs076-binary inner x x)
                     scalar-zero)))
      (iff
       (equal (fs076-binary inner x x) scalar-zero)
       (equal x zero))))))

(defun fs076-norm-lt-p
    (scalar-multiply less add negate inner x y epsilon)
  (apply$
   less
   (list
    (fs076-binary
     inner
     (fs076-vector-difference add negate x y)
     (fs076-vector-difference add negate x y))
    (fs076-binary scalar-multiply epsilon epsilon))))

(defun-sk fs076-sequence-values-p (carrier sequence)
  (forall (n)
    (implies
     (natp n)
     (fs076-member-p carrier
                     (apply$ sequence (list n))))))

(defun-sk fs076-cauchy-tail-p
    (scalar-multiply less add negate inner sequence epsilon cutoff)
  (forall (m n)
    (implies
     (and (natp m)
          (natp n)
          (<= cutoff m)
          (<= cutoff n))
     (fs076-norm-lt-p
      scalar-multiply less add negate inner
      (apply$ sequence (list m))
      (apply$ sequence (list n))
      epsilon))))

(defun-sk fs076-cauchy-cutoff-exists-p
    (scalar-multiply less add negate inner sequence epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (fs076-cauchy-tail-p
      scalar-multiply less add negate inner
      sequence epsilon cutoff))))

(defun-sk fs076-cauchy-p
    (scalar-carrier scalar-multiply scalar-zero less
     add negate inner sequence)
  (forall (epsilon)
    (implies
     (fs076-positive-p
      scalar-carrier less scalar-zero epsilon)
     (fs076-cauchy-cutoff-exists-p
      scalar-multiply less add negate inner
      sequence epsilon))))

(defun-sk fs076-convergence-tail-p
    (scalar-multiply less add negate inner
     sequence limit epsilon cutoff)
  (forall (n)
    (implies
     (and (natp n)
          (<= cutoff n))
     (fs076-norm-lt-p
      scalar-multiply less add negate inner
      (apply$ sequence (list n))
      limit epsilon))))

(defun-sk fs076-convergence-cutoff-exists-p
    (scalar-multiply less add negate inner
     sequence limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (fs076-convergence-tail-p
      scalar-multiply less add negate inner
      sequence limit epsilon cutoff))))

(defun-sk fs076-converges-p
    (scalar-carrier scalar-multiply scalar-zero less
     carrier add negate inner sequence limit)
  (forall (epsilon)
    (implies
     (fs076-positive-p
      scalar-carrier less scalar-zero epsilon)
     (fs076-convergence-cutoff-exists-p
      scalar-multiply less add negate inner
      sequence limit epsilon))))

(defun-sk fs076-limit-exists-p
    (scalar-carrier scalar-multiply scalar-zero less
     carrier add negate inner sequence)
  (exists (limit)
    (and
     (fs076-member-p carrier limit)
     (fs076-converges-p
      scalar-carrier scalar-multiply scalar-zero less
      carrier add negate inner sequence limit))))

(defun-sk fs076-complete-p
    (scalar-carrier scalar-multiply scalar-zero less
     carrier add negate inner)
  (forall (sequence)
    (implies
     (and
      (tamep-functionp sequence)
      (fs076-sequence-values-p carrier sequence)
      (fs076-cauchy-p
       scalar-carrier scalar-multiply scalar-zero less
       add negate inner sequence))
     (fs076-limit-exists-p
      scalar-carrier scalar-multiply scalar-zero less
      carrier add negate inner sequence))))

(defun fs076-hilbert-space-p
    (scalar-carrier scalar-add scalar-multiply
     scalar-zero scalar-one less
     carrier add negate zero smul inner)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp negate)
   (tamep-functionp smul)
   (tamep-functionp inner)
   (fs076-member-p carrier zero)
   (fs076-vector-space-laws-p
    scalar-carrier scalar-add scalar-multiply scalar-one
    carrier add negate zero smul)
   (fs076-inner-product-laws-p
    scalar-carrier scalar-add scalar-multiply scalar-zero less
    carrier add zero smul inner)
   (fs076-complete-p
    scalar-carrier scalar-multiply scalar-zero less
    carrier add negate inner)))

(defun-sk fs076-basis-values-p (carrier basis)
  (forall (n)
    (implies
     (natp n)
     (fs076-member-p carrier
                     (apply$ basis (list n))))))

(defun-sk fs076-orthonormal-p
    (scalar-zero scalar-one carrier inner basis)
  (forall (m n)
    (implies
     (and (natp m)
          (natp n)
          (fs076-member-p carrier
                          (apply$ basis (list m)))
          (fs076-member-p carrier
                          (apply$ basis (list n))))
     (equal
      (fs076-binary
       inner
       (apply$ basis (list m))
       (apply$ basis (list n)))
      (if (equal m n) scalar-one scalar-zero)))))

(defun fs076-scalar-list-p (scalar-carrier coefficients)
  (if (consp coefficients)
      (and
       (fs076-member-p scalar-carrier (car coefficients))
       (fs076-scalar-list-p
        scalar-carrier (cdr coefficients)))
    (equal coefficients nil)))

(defun fs076-linear-combination
    (basis coefficients count add zero smul)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (let ((index (- count 1)))
      (fs076-binary
       add
       (fs076-linear-combination
        basis coefficients index add zero smul)
       (fs076-binary
        smul
        (nth index coefficients)
        (apply$ basis (list index)))))))

(defun-sk fs076-dense-witness-exists-p
    (scalar-carrier scalar-multiply scalar-zero less
     carrier add negate zero smul inner basis f epsilon)
  (exists (count coefficients)
    (and
     (natp count)
     (true-listp coefficients)
     (equal (len coefficients) count)
     (fs076-scalar-list-p
      scalar-carrier coefficients)
     (fs076-norm-lt-p
      scalar-multiply less add negate inner
      (fs076-linear-combination
       basis coefficients count add zero smul)
      f epsilon))))

(defun-sk fs076-dense-span-p
    (scalar-carrier scalar-multiply scalar-zero less
     carrier add negate zero smul inner basis)
  (forall (f epsilon)
    (implies
     (and
      (fs076-member-p carrier f)
      (fs076-positive-p
       scalar-carrier less scalar-zero epsilon))
     (fs076-dense-witness-exists-p
      scalar-carrier scalar-multiply scalar-zero less
      carrier add negate zero smul inner basis f epsilon))))

(defun fs076-fourier-basis-p
    (scalar-carrier scalar-multiply scalar-zero scalar-one less
     carrier add negate zero smul inner basis)
  (and
   (tamep-functionp basis)
   (fs076-basis-values-p carrier basis)
   (fs076-orthonormal-p
    scalar-zero scalar-one carrier inner basis)
   (fs076-dense-span-p
    scalar-carrier scalar-multiply scalar-zero less
    carrier add negate zero smul inner basis)))

(defun fs076-fourier-partial-sum
    (basis f count add zero smul inner)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (let ((index (- count 1)))
      (fs076-binary
       add
       (fs076-fourier-partial-sum
        basis f index add zero smul inner)
       (fs076-binary
        smul
        (fs076-binary
         inner (apply$ basis (list index)) f)
        (apply$ basis (list index)))))))

(defun-sk fs076-fourier-tail-p
    (scalar-multiply less add negate zero smul inner
     basis f epsilon cutoff)
  (forall (count)
    (implies
     (and (natp count)
          (<= cutoff count))
     (fs076-norm-lt-p
      scalar-multiply less add negate inner
      (fs076-fourier-partial-sum
       basis f count add zero smul inner)
      f epsilon))))

(defun-sk fs076-fourier-cutoff-exists-p
    (scalar-multiply less add negate zero smul inner
     basis f epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (fs076-fourier-tail-p
      scalar-multiply less add negate zero smul inner
      basis f epsilon cutoff))))

(defun-sk fs076-fourier-converges-p
    (scalar-carrier scalar-multiply scalar-zero less
     carrier add negate zero smul inner basis)
  (forall (f epsilon)
    (implies
     (and
      (fs076-member-p carrier f)
      (fs076-positive-p
       scalar-carrier less scalar-zero epsilon))
     (fs076-fourier-cutoff-exists-p
      scalar-multiply less add negate zero smul inner
      basis f epsilon))))

(defun hundred-theorems-076-fourier-series-statement
    (real-carrier real-add real-multiply real-negate real-inverse
     real-zero real-one real-less
     l2-carrier l2-add l2-negate l2-zero l2-smul l2-inner
     trigonometric-basis)
  (implies
   (and
    (fs076-real-field-p
     real-carrier real-add real-multiply real-negate real-inverse
     real-zero real-one real-less)
    (fs076-hilbert-space-p
     real-carrier real-add real-multiply real-zero real-one real-less
     l2-carrier l2-add l2-negate l2-zero l2-smul l2-inner)
    (fs076-fourier-basis-p
     real-carrier real-multiply real-zero real-one real-less
     l2-carrier l2-add l2-negate l2-zero l2-smul l2-inner
     trigonometric-basis))
   (fs076-fourier-converges-p
    real-carrier real-multiply real-zero real-less
    l2-carrier l2-add l2-negate l2-zero l2-smul l2-inner
    trigonometric-basis)))

(value-triple :itpeval-statement-checked)
:q
