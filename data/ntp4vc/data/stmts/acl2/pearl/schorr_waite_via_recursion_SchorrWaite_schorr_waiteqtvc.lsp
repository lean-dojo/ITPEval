; Statement-only formalization of the ntp4vc corpus artifact
; pearl/schorr_waite_via_recursion_SchorrWaite_schorr_waiteqtvc: the
; Schorr-Waite graph-marking verification condition via recursive traversal,
; including functional memory updates, path/color invariants, finite gray
; sets, loop variants, and final reachability guarantees. This file contains
; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

; Locations and memories remain arbitrary inhabited source domains.
(defstub swvr-loc-p (*) => *)
(defstub swvr-memory-p (*) => *)
(defstub swvr-null () => *)

; The three source record fields are arbitrary total maps.
(defstub swvr-block-size (* *) => *)
(defstub swvr-accessor (* * *) => *)
(defstub swvr-colors (* *) => *)

(defun swvr-black-none ()
  (list :black :none))

(defun swvr-black-some (i)
  (list :black (list :some i)))

(defun swvr-black-some-p (c)
  (and (consp c)
       (equal (car c) :black)
       (consp (cdr c))
       (consp (car (cdr c)))
       (equal (car (car (cdr c))) :some)
       (consp (cdr (car (cdr c))))
       (integerp (car (cdr (car (cdr c)))))
       (equal (cdr (cdr (car (cdr c)))) nil)
       (equal (cdr (cdr c)) nil)))

(defun swvr-black-index (c)
  (car (cdr (car (cdr c)))))

(defun swvr-color-p (c)
  (or (equal c :white)
      (equal c (swvr-black-none))
      (swvr-black-some-p c)))

(defun swvr-black-p (c)
  (not (equal c :white)))

(defun swvr-loc-list-p (xs)
  (if (consp xs)
      (and (swvr-loc-p (car xs))
           (swvr-loc-list-p (cdr xs)))
    (equal xs nil)))

; Only source finite sets are represented by duplicate-free lists.
(defun swvr-loc-fset-p (xs)
  (if (consp xs)
      (and (swvr-loc-p (car xs))
           (not (member-equal (car xs) (cdr xs)))
           (swvr-loc-fset-p (cdr xs)))
    (equal xs nil)))

(defun swvr-fset-insert (x xs)
  (if (member-equal x xs)
      xs
    (cons x xs)))

(defun-sk swvr-interface-typed-p ()
  (forall (m x n)
    (implies
     (and (swvr-memory-p m)
          (swvr-loc-p x)
          (integerp n))
     (and (integerp (swvr-block-size m x))
          (swvr-loc-p (swvr-accessor m x n))
          (swvr-color-p (swvr-colors m x))))))

(defun-sk swvr-edge-p (m x y)
  (exists (n)
    (and (integerp n)
         (not (equal x (swvr-null)))
         (<= 0 n)
         (< n (swvr-block-size m x))
         (equal (swvr-accessor m x n) y))))

(defun swvr-path-chain-p (m xs)
  (if (and (consp xs) (consp (cdr xs)))
      (and (swvr-edge-p m (car xs) (car (cdr xs)))
           (swvr-path-chain-p m (cdr xs)))
    (and (consp xs) (equal (cdr xs) nil))))

; A nonempty finite edge sequence is equivalent to the source inductive path.
(defun-sk swvr-path-p (m x y)
  (exists (xs)
    (and (swvr-loc-list-p xs)
         (consp xs)
         (equal (car xs) x)
         (equal (car (last xs)) y)
         (swvr-path-chain-p m xs))))

(defun swvr-subset-p (xs ys)
  (if (consp xs)
      (and (member-equal (car xs) ys)
           (swvr-subset-p (cdr xs) ys))
    (equal xs nil)))

(defun-sk swvr-well-colored-edge-p (graph gray old-memory color-memory)
  (forall (x y)
    (implies
     (and (swvr-loc-p x)
          (swvr-loc-p y)
          (member-equal x graph)
          (swvr-edge-p old-memory x y)
          (not (equal y (swvr-null)))
          (swvr-black-p (swvr-colors color-memory x)))
     (or (member-equal x gray)
         (swvr-black-p (swvr-colors color-memory y))))))

(defun-sk swvr-well-colored-gray-p (gray color-memory)
  (forall (x)
    (implies
     (and (swvr-loc-p x)
          (member-equal x gray))
     (swvr-black-p (swvr-colors color-memory x)))))

(defun swvr-well-colored-on-p (graph gray old-memory color-memory)
  (and (swvr-subset-p gray graph)
       (swvr-well-colored-edge-p graph gray old-memory color-memory)
       (swvr-well-colored-gray-p gray color-memory)))

(defun-sk swvr-unchanged-p (m1 m2)
  (forall (x n)
    (implies
     (and (swvr-loc-p x)
          (not (equal x (swvr-null)))
          (integerp n)
          (<= 0 n)
          (< n (swvr-block-size m1 x)))
     (equal (swvr-accessor m2 x n)
            (swvr-accessor m1 x n)))))

(defun swvr-forall-0001-body (graph memo l n)
  (implies (and (swvr-loc-p l) (integerp n)) (implies (and (member-equal l graph) (not (equal l (swvr-null))) (<= 0 n) (< n (swvr-block-size memo l))) (member-equal (swvr-accessor memo l n) graph))))

(defun-sk swvr-forall-0001 (graph memo)
  (forall (l n)
    (swvr-forall-0001-body graph memo l n)))

(defun swvr-forall-0002-body (graph memo x)
  (implies (and (swvr-loc-p x)) (implies (member-equal x graph) (not (swvr-black-p (swvr-colors memo x))))))

(defun-sk swvr-forall-0002 (graph memo)
  (forall (x)
    (swvr-forall-0002-body graph memo x)))

(defun-sk swvr-bmap-eq-0003 (memo memo1)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo1 swvr-x) (swvr-block-size memo swvr-x)))))

(defun-sk swvr-bmap-eq-0004 (memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo2 swvr-x) (swvr-block-size memo1 swvr-x)))))

(defun-sk swvr-cmap-eq-0005 (memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (swvr-colors memo1 swvr-x)))))

(defun-sk swvr-amap-eq-0006 (p swvr-v-t memo1 m memo2)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (if (equal swvr-x p) (if (equal swvr-n m) swvr-v-t (swvr-accessor memo1 p swvr-n)) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0007 (swvr-v-t memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (if (equal swvr-x swvr-v-t) (swvr-black-none) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0008 (memo1 memo2)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (swvr-accessor memo1 swvr-x swvr-n)))))

(defun-sk swvr-cmap-eq-0009 (swvr-v-t memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (if (equal swvr-x swvr-v-t) (swvr-black-some 0) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0010 (p swvr-v-t memo1 memo2)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (if (equal swvr-x swvr-v-t) (if (equal swvr-n 0) p (swvr-accessor memo1 swvr-v-t swvr-n)) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0011 (memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (swvr-colors memo1 swvr-x)))))

(defun-sk swvr-amap-eq-0012 (p swvr-v-t memo1 memo2 m1)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (if (equal swvr-x p) (if (equal swvr-n m1) swvr-v-t (swvr-accessor memo1 p swvr-n)) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0013 (p memo1 memo2 n1)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (if (equal swvr-x p) (swvr-black-some n1) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0014 (p swvr-v-t memo1 memo2 m1 n1)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (if (equal swvr-x p) (if (equal swvr-n m1) swvr-v-t (if (equal swvr-n n1) (swvr-accessor memo1 p m1) (swvr-accessor memo1 p swvr-n))) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun swvr-forall-0015-body (p swvr-v-t memo1 m memo2)
  (implies (and (swvr-memory-p memo2)) (implies (and (swvr-bmap-eq-0004 memo1 memo2) (swvr-cmap-eq-0005 memo1 memo2)) (implies (swvr-amap-eq-0006 p swvr-v-t memo1 m memo2) (and (or (not (equal p (swvr-null))) (and (not (equal swvr-v-t (swvr-null))) (not (swvr-black-p (swvr-colors memo1 swvr-v-t))))) (implies (and (not (equal swvr-v-t (swvr-null))) (not (swvr-black-p (swvr-colors memo1 swvr-v-t))) (equal (swvr-block-size memo1 swvr-v-t) 0)) (and (swvr-cmap-eq-0007 swvr-v-t memo1 memo2) (equal p swvr-v-t) (equal (swvr-accessor memo1 p m) p) (swvr-amap-eq-0008 memo1 memo2))) (implies (and (not (equal swvr-v-t (swvr-null))) (not (swvr-black-p (swvr-colors memo1 swvr-v-t))) (< 0 (swvr-block-size memo1 swvr-v-t))) (and (swvr-cmap-eq-0009 swvr-v-t memo1 memo2) (equal p (swvr-accessor memo1 swvr-v-t 0)) (equal (swvr-accessor memo1 p m) swvr-v-t) (swvr-amap-eq-0010 p swvr-v-t memo1 memo2))) (implies (or (equal swvr-v-t (swvr-null)) (swvr-black-p (swvr-colors memo1 swvr-v-t))) (if (swvr-black-some-p (swvr-colors memo1 p)) (let ((m1 (swvr-black-index (swvr-colors memo1 p)))) (let ((n1 (+ m1 1))) (if (equal n1 (swvr-block-size memo1 p)) (and (equal (swvr-accessor memo1 p m) (swvr-accessor memo1 p m1)) (swvr-cmap-eq-0011 memo1 memo2) (swvr-amap-eq-0012 p swvr-v-t memo1 memo2 m1)) (and (equal (swvr-accessor memo1 p m) p) (equal p (swvr-accessor memo1 p n1)) (swvr-cmap-eq-0013 p memo1 memo2 n1) (swvr-amap-eq-0014 p swvr-v-t memo1 memo2 m1 n1))))) nil)))))))

(defun-sk swvr-forall-0015 (p swvr-v-t memo1 m)
  (forall (memo2)
    (swvr-forall-0015-body p swvr-v-t memo1 m memo2)))

(defun-sk swvr-bmap-eq-0016 (memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo2 swvr-x) (swvr-block-size memo1 swvr-x)))))

(defun-sk swvr-cmap-eq-0017 (memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (swvr-colors memo1 swvr-x)))))

(defun-sk swvr-amap-eq-0018 (p memo1 m n memo2)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (if (equal swvr-x p) (if (equal swvr-n n) (swvr-accessor memo1 p m) (swvr-accessor memo1 p swvr-n)) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun-sk swvr-bmap-eq-0019 (memo2 memo3)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo3 swvr-x) (swvr-block-size memo2 swvr-x)))))

(defun-sk swvr-cmap-eq-0020 (memo2 memo3)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo3 swvr-x) (swvr-colors memo2 swvr-x)))))

(defun-sk swvr-amap-eq-0021 (p swvr-v-t m memo2 memo3)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo3 swvr-x swvr-n) (if (equal swvr-x p) (if (equal swvr-n m) swvr-v-t (swvr-accessor memo2 p swvr-n)) (swvr-accessor memo2 swvr-x swvr-n))))))

(defun-sk swvr-bmap-eq-0022 (memo3 memo4)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo4 swvr-x) (swvr-block-size memo3 swvr-x)))))

(defun-sk swvr-amap-eq-0023 (memo3 memo4)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo4 swvr-x swvr-n) (swvr-accessor memo3 swvr-x swvr-n)))))

(defun-sk swvr-cmap-eq-0024 (p n memo3 memo4)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo4 swvr-x) (if (equal swvr-x p) (swvr-black-some n) (swvr-colors memo3 swvr-x))))))

(defun-sk swvr-cmap-eq-0025 (swvr-v-t memo1 memo4)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo4 swvr-x) (if (equal swvr-x swvr-v-t) (swvr-black-none) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0026 (memo1 memo4)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo4 swvr-x swvr-n) (swvr-accessor memo1 swvr-x swvr-n)))))

(defun-sk swvr-cmap-eq-0027 (swvr-v-t memo1 memo4)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo4 swvr-x) (if (equal swvr-x swvr-v-t) (swvr-black-some 0) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0028 (p swvr-v-t memo1 memo4)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo4 swvr-x swvr-n) (if (equal swvr-x swvr-v-t) (if (equal swvr-n 0) p (swvr-accessor memo1 swvr-v-t swvr-n)) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0029 (memo1 memo4)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo4 swvr-x) (swvr-colors memo1 swvr-x)))))

(defun-sk swvr-amap-eq-0030 (p swvr-v-t memo1 memo4 m1)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo4 swvr-x swvr-n) (if (equal swvr-x p) (if (equal swvr-n m1) swvr-v-t (swvr-accessor memo1 p swvr-n)) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0031 (p memo1 memo4 n1)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo4 swvr-x) (if (equal swvr-x p) (swvr-black-some n1) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0032 (p swvr-v-t memo1 memo4 m1 n1)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo4 swvr-x swvr-n) (if (equal swvr-x p) (if (equal swvr-n m1) swvr-v-t (if (equal swvr-n n1) (swvr-accessor memo1 p m1) (swvr-accessor memo1 p swvr-n))) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun swvr-forall-0033-body (p swvr-v-t memo1 n memo3 memo4)
  (implies (and (swvr-memory-p memo4)) (implies (and (swvr-bmap-eq-0022 memo3 memo4) (swvr-amap-eq-0023 memo3 memo4)) (implies (swvr-cmap-eq-0024 p n memo3 memo4) (and (or (not (equal p (swvr-null))) (and (not (equal swvr-v-t (swvr-null))) (not (swvr-black-p (swvr-colors memo1 swvr-v-t))))) (implies (and (not (equal swvr-v-t (swvr-null))) (not (swvr-black-p (swvr-colors memo1 swvr-v-t))) (equal (swvr-block-size memo1 swvr-v-t) 0)) (and (swvr-cmap-eq-0025 swvr-v-t memo1 memo4) (equal (swvr-accessor memo1 p n) swvr-v-t) (swvr-amap-eq-0026 memo1 memo4))) (implies (and (not (equal swvr-v-t (swvr-null))) (not (swvr-black-p (swvr-colors memo1 swvr-v-t))) (< 0 (swvr-block-size memo1 swvr-v-t))) (and (swvr-cmap-eq-0027 swvr-v-t memo1 memo4) (equal (swvr-accessor memo1 p n) (swvr-accessor memo1 swvr-v-t 0)) (equal p swvr-v-t) (swvr-amap-eq-0028 p swvr-v-t memo1 memo4))) (implies (or (equal swvr-v-t (swvr-null)) (swvr-black-p (swvr-colors memo1 swvr-v-t))) (if (swvr-black-some-p (swvr-colors memo1 p)) (let ((m1 (swvr-black-index (swvr-colors memo1 p)))) (let ((n1 (+ m1 1))) (if (equal n1 (swvr-block-size memo1 p)) (and (equal (swvr-accessor memo1 p n) p) (equal p (swvr-accessor memo1 p m1)) (swvr-cmap-eq-0029 memo1 memo4) (swvr-amap-eq-0030 p swvr-v-t memo1 memo4 m1)) (and (equal (swvr-accessor memo1 p n) (swvr-accessor memo1 p n1)) (swvr-cmap-eq-0031 p memo1 memo4 n1) (swvr-amap-eq-0032 p swvr-v-t memo1 memo4 m1 n1))))) nil)))))))

(defun-sk swvr-forall-0033 (p swvr-v-t memo1 n memo3)
  (forall (memo4)
    (swvr-forall-0033-body p swvr-v-t memo1 n memo3 memo4)))

(defun swvr-forall-0034-body (p swvr-v-t memo1 m n memo2 memo3)
  (implies (and (swvr-memory-p memo3)) (implies (and (swvr-bmap-eq-0019 memo2 memo3) (swvr-cmap-eq-0020 memo2 memo3)) (implies (swvr-amap-eq-0021 p swvr-v-t m memo2 memo3) (and (and (not (equal p (swvr-null))) (<= 0 n) (< n (swvr-block-size memo3 p))) (swvr-forall-0033 p swvr-v-t memo1 n memo3))))))

(defun-sk swvr-forall-0034 (p swvr-v-t memo1 m n memo2)
  (forall (memo3)
    (swvr-forall-0034-body p swvr-v-t memo1 m n memo2 memo3)))

(defun swvr-forall-0035-body (p swvr-v-t memo1 m n memo2)
  (implies (and (swvr-memory-p memo2)) (implies (and (swvr-bmap-eq-0016 memo1 memo2) (swvr-cmap-eq-0017 memo1 memo2)) (implies (swvr-amap-eq-0018 p memo1 m n memo2) (and (and (not (equal p (swvr-null))) (<= 0 m) (< m (swvr-block-size memo2 p))) (swvr-forall-0034 p swvr-v-t memo1 m n memo2))))))

(defun-sk swvr-forall-0035 (p swvr-v-t memo1 m n)
  (forall (memo2)
    (swvr-forall-0035-body p swvr-v-t memo1 m n memo2)))

(defun-sk swvr-bmap-eq-0036 (memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo2 swvr-x) (swvr-block-size memo1 swvr-x)))))

(defun-sk swvr-amap-eq-0037 (memo1 memo2)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (swvr-accessor memo1 swvr-x swvr-n)))))

(defun-sk swvr-cmap-eq-0038 (swvr-v-t memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (if (equal swvr-x swvr-v-t) (swvr-black-none) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-cmap-eq-0039 (swvr-v-t memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (if (equal swvr-x swvr-v-t) (swvr-black-none) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0040 (memo1 memo2)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (swvr-accessor memo1 swvr-x swvr-n)))))

(defun-sk swvr-cmap-eq-0041 (swvr-v-t memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (if (equal swvr-x swvr-v-t) (swvr-black-some 0) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0042 (p swvr-v-t memo1 memo2)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (if (equal swvr-x swvr-v-t) (if (equal swvr-n 0) p (swvr-accessor memo1 swvr-v-t swvr-n)) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0043 (memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (swvr-colors memo1 swvr-x)))))

(defun-sk swvr-amap-eq-0044 (p swvr-v-t memo1 memo2 m)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (if (equal swvr-x p) (if (equal swvr-n m) swvr-v-t (swvr-accessor memo1 p swvr-n)) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0045 (p memo1 memo2 n)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (if (equal swvr-x p) (swvr-black-some n) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0046 (p swvr-v-t memo1 memo2 m n)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (if (equal swvr-x p) (if (equal swvr-n m) swvr-v-t (if (equal swvr-n n) (swvr-accessor memo1 p m) (swvr-accessor memo1 p swvr-n))) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun swvr-forall-0047-body (p swvr-v-t memo1 memo2)
  (implies (and (swvr-memory-p memo2)) (implies (and (swvr-bmap-eq-0036 memo1 memo2) (swvr-amap-eq-0037 memo1 memo2)) (implies (swvr-cmap-eq-0038 swvr-v-t memo1 memo2) (and (or (not (equal p (swvr-null))) (and (not (equal swvr-v-t (swvr-null))) (not (swvr-black-p (swvr-colors memo1 swvr-v-t))))) (implies (and (not (equal swvr-v-t (swvr-null))) (not (swvr-black-p (swvr-colors memo1 swvr-v-t))) (equal (swvr-block-size memo1 swvr-v-t) 0)) (and (swvr-cmap-eq-0039 swvr-v-t memo1 memo2) (swvr-amap-eq-0040 memo1 memo2))) (implies (and (not (equal swvr-v-t (swvr-null))) (not (swvr-black-p (swvr-colors memo1 swvr-v-t))) (< 0 (swvr-block-size memo1 swvr-v-t))) (and (swvr-cmap-eq-0041 swvr-v-t memo1 memo2) (equal swvr-v-t (swvr-accessor memo1 swvr-v-t 0)) (equal p swvr-v-t) (swvr-amap-eq-0042 p swvr-v-t memo1 memo2))) (implies (or (equal swvr-v-t (swvr-null)) (swvr-black-p (swvr-colors memo1 swvr-v-t))) (if (swvr-black-some-p (swvr-colors memo1 p)) (let ((m (swvr-black-index (swvr-colors memo1 p)))) (let ((n (+ m 1))) (if (equal n (swvr-block-size memo1 p)) (and (equal swvr-v-t p) (equal p (swvr-accessor memo1 p m)) (swvr-cmap-eq-0043 memo1 memo2) (swvr-amap-eq-0044 p swvr-v-t memo1 memo2 m)) (and (equal swvr-v-t (swvr-accessor memo1 p n)) (swvr-cmap-eq-0045 p memo1 memo2 n) (swvr-amap-eq-0046 p swvr-v-t memo1 memo2 m n))))) nil)))))))

(defun-sk swvr-forall-0047 (p swvr-v-t memo1)
  (forall (memo2)
    (swvr-forall-0047-body p swvr-v-t memo1 memo2)))

(defun-sk swvr-bmap-eq-0048 (memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo2 swvr-x) (swvr-block-size memo1 swvr-x)))))

(defun-sk swvr-cmap-eq-0049 (memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (swvr-colors memo1 swvr-x)))))

(defun-sk swvr-amap-eq-0050 (p swvr-v-t memo1 memo2)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (if (equal swvr-x swvr-v-t) (if (equal swvr-n 0) p (swvr-accessor memo1 swvr-v-t swvr-n)) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun-sk swvr-bmap-eq-0051 (memo2 memo3)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo3 swvr-x) (swvr-block-size memo2 swvr-x)))))

(defun-sk swvr-amap-eq-0052 (memo2 memo3)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo3 swvr-x swvr-n) (swvr-accessor memo2 swvr-x swvr-n)))))

(defun-sk swvr-cmap-eq-0053 (swvr-v-t memo2 memo3)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo3 swvr-x) (if (equal swvr-x swvr-v-t) (swvr-black-some 0) (swvr-colors memo2 swvr-x))))))

(defun-sk swvr-cmap-eq-0054 (swvr-v-t memo1 memo3)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo3 swvr-x) (if (equal swvr-x swvr-v-t) (swvr-black-none) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0055 (memo1 memo3)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo3 swvr-x swvr-n) (swvr-accessor memo1 swvr-x swvr-n)))))

(defun-sk swvr-cmap-eq-0056 (swvr-v-t memo1 memo3)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo3 swvr-x) (if (equal swvr-x swvr-v-t) (swvr-black-some 0) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0057 (p swvr-v-t memo1 memo3)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo3 swvr-x swvr-n) (if (equal swvr-x swvr-v-t) (if (equal swvr-n 0) p (swvr-accessor memo1 swvr-v-t swvr-n)) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0058 (memo1 memo3)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo3 swvr-x) (swvr-colors memo1 swvr-x)))))

(defun-sk swvr-amap-eq-0059 (p swvr-v-t memo1 memo3 m)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo3 swvr-x swvr-n) (if (equal swvr-x p) (if (equal swvr-n m) swvr-v-t (swvr-accessor memo1 p swvr-n)) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0060 (p memo1 memo3 n)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo3 swvr-x) (if (equal swvr-x p) (swvr-black-some n) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0061 (p swvr-v-t memo1 memo3 m n)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo3 swvr-x swvr-n) (if (equal swvr-x p) (if (equal swvr-n m) swvr-v-t (if (equal swvr-n n) (swvr-accessor memo1 p m) (swvr-accessor memo1 p swvr-n))) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun swvr-forall-0062-body (p swvr-v-t memo1 memo2 memo3)
  (implies (and (swvr-memory-p memo3)) (implies (and (swvr-bmap-eq-0051 memo2 memo3) (swvr-amap-eq-0052 memo2 memo3)) (implies (swvr-cmap-eq-0053 swvr-v-t memo2 memo3) (and (or (not (equal p (swvr-null))) (and (not (equal swvr-v-t (swvr-null))) (not (swvr-black-p (swvr-colors memo1 swvr-v-t))))) (implies (and (not (equal swvr-v-t (swvr-null))) (not (swvr-black-p (swvr-colors memo1 swvr-v-t))) (equal (swvr-block-size memo1 swvr-v-t) 0)) (and (swvr-cmap-eq-0054 swvr-v-t memo1 memo3) (equal (swvr-accessor memo1 swvr-v-t 0) swvr-v-t) (equal swvr-v-t p) (swvr-amap-eq-0055 memo1 memo3))) (implies (and (not (equal swvr-v-t (swvr-null))) (not (swvr-black-p (swvr-colors memo1 swvr-v-t))) (< 0 (swvr-block-size memo1 swvr-v-t))) (and (swvr-cmap-eq-0056 swvr-v-t memo1 memo3) (swvr-amap-eq-0057 p swvr-v-t memo1 memo3))) (implies (or (equal swvr-v-t (swvr-null)) (swvr-black-p (swvr-colors memo1 swvr-v-t))) (if (swvr-black-some-p (swvr-colors memo1 p)) (let ((m (swvr-black-index (swvr-colors memo1 p)))) (let ((n (+ m 1))) (if (equal n (swvr-block-size memo1 p)) (and (equal (swvr-accessor memo1 swvr-v-t 0) p) (equal swvr-v-t (swvr-accessor memo1 p m)) (swvr-cmap-eq-0058 memo1 memo3) (swvr-amap-eq-0059 p swvr-v-t memo1 memo3 m)) (and (equal swvr-v-t p) (equal (swvr-accessor memo1 swvr-v-t 0) (swvr-accessor memo1 p n)) (swvr-cmap-eq-0060 p memo1 memo3 n) (swvr-amap-eq-0061 p swvr-v-t memo1 memo3 m n))))) nil)))))))

(defun-sk swvr-forall-0062 (p swvr-v-t memo1 memo2)
  (forall (memo3)
    (swvr-forall-0062-body p swvr-v-t memo1 memo2 memo3)))

(defun swvr-forall-0063-body (p swvr-v-t memo1 memo2)
  (implies (and (swvr-memory-p memo2)) (implies (and (swvr-bmap-eq-0048 memo1 memo2) (swvr-cmap-eq-0049 memo1 memo2)) (implies (swvr-amap-eq-0050 p swvr-v-t memo1 memo2) (and (and (not (equal swvr-v-t (swvr-null))) (<= 0 0) (< 0 (swvr-block-size memo2 swvr-v-t))) (swvr-forall-0062 p swvr-v-t memo1 memo2))))))

(defun-sk swvr-forall-0063 (p swvr-v-t memo1)
  (forall (memo2)
    (swvr-forall-0063-body p swvr-v-t memo1 memo2)))

(defun swvr-forall-0064-body (p swvr-v-t memo1 o2)
  (implies (and (booleanp o2)) (implies (if (equal swvr-v-t (swvr-null)) (equal o2 t) (equal o2 (if (swvr-black-p (swvr-colors memo1 swvr-v-t)) t nil))) (if (equal o2 t) (and (not (equal p (swvr-null))) (if (swvr-black-some-p (swvr-colors memo1 p)) (let ((m (swvr-black-index (swvr-colors memo1 p)))) (and (not (equal p (swvr-null))) (let ((s (swvr-block-size memo1 p))) (implies (<= 0 s) (let ((n (+ m 1))) (if (equal n s) (and (and (not (equal p (swvr-null))) (<= 0 m) (< m (swvr-block-size memo1 p))) (and (not (equal p (swvr-null))) (<= 0 m) (< m (swvr-block-size memo1 p))) (swvr-forall-0015 p swvr-v-t memo1 m)) (and (and (not (equal p (swvr-null))) (<= 0 n) (< n (swvr-block-size memo1 p))) (and (not (equal p (swvr-null))) (<= 0 m) (< m (swvr-block-size memo1 p))) (and (not (equal p (swvr-null))) (<= 0 n) (< n (swvr-block-size memo1 p))) (swvr-forall-0035 p swvr-v-t memo1 m n)))))))) nil)) (and (not (equal swvr-v-t (swvr-null))) (let ((s (swvr-block-size memo1 swvr-v-t))) (implies (<= 0 s) (if (equal s 0) (and (and (not (equal swvr-v-t (swvr-null))) (equal (swvr-block-size memo1 swvr-v-t) 0)) (swvr-forall-0047 p swvr-v-t memo1)) (and (and (not (equal swvr-v-t (swvr-null))) (<= 0 0) (< 0 (swvr-block-size memo1 swvr-v-t))) (and (not (equal swvr-v-t (swvr-null))) (<= 0 0) (< 0 (swvr-block-size memo1 swvr-v-t))) (swvr-forall-0063 p swvr-v-t memo1))))))))))

(defun-sk swvr-forall-0064 (p swvr-v-t memo1)
  (forall (o2)
    (swvr-forall-0064-body p swvr-v-t memo1 o2)))

(defun swvr-forall-0065-body (p swvr-v-t memo1 o1)
  (implies (and (booleanp o1)) (implies (if (equal p (swvr-null)) (if (equal swvr-v-t (swvr-null)) (equal o1 t) (equal o1 (if (swvr-black-p (swvr-colors memo1 swvr-v-t)) t nil))) (equal o1 nil)) (if (equal o1 t) (and (equal p (swvr-null)) (or (equal swvr-v-t (swvr-null)) (swvr-black-p (swvr-colors memo1 swvr-v-t)))) (swvr-forall-0064 p swvr-v-t memo1)))))

(defun-sk swvr-forall-0065 (p swvr-v-t memo1)
  (forall (o1)
    (swvr-forall-0065-body p swvr-v-t memo1 o1)))

(defun swvr-forall-0066-body (memo p swvr-v-t memo1)
  (implies (and (swvr-loc-p p) (swvr-loc-p swvr-v-t) (swvr-memory-p memo1)) (implies (swvr-bmap-eq-0003 memo memo1) (implies (implies (and (not (equal p (swvr-null))) (or (equal swvr-v-t (swvr-null)) (swvr-black-p (swvr-colors memo1 swvr-v-t)))) (if (swvr-black-some-p (swvr-colors memo1 p)) (let ((m (swvr-black-index (swvr-colors memo1 p)))) (and (<= 0 m) (< m (swvr-block-size memo1 p)))) nil)) (swvr-forall-0065 p swvr-v-t memo1)))))

(defun-sk swvr-forall-0066 (memo)
  (forall (p swvr-v-t memo1)
    (swvr-forall-0066-body memo p swvr-v-t memo1)))

(defun-sk swvr-bmap-eq-0067 (memo memo1)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo1 swvr-x) (swvr-block-size memo swvr-x)))))

(defun swvr-forall-0068-body (memo memo1 x n)
  (implies (and (swvr-loc-p x) (integerp n)) (implies (and (not (equal x (swvr-null))) (not (swvr-black-p (swvr-colors memo1 x))) (<= 0 n) (< n (swvr-block-size memo1 x))) (equal (swvr-accessor memo1 x n) (swvr-accessor memo x n)))))

(defun-sk swvr-forall-0068 (memo memo1)
  (forall (x n)
    (swvr-forall-0068-body memo memo1 x n)))

(defun-sk swvr-bmap-eq-0069 (memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo2 swvr-x) (swvr-block-size memo1 swvr-x)))))

(defun-sk swvr-cmap-eq-0070 (swvr-v-t memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (if (equal swvr-x swvr-v-t) (swvr-black-none) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0071 (memo1 memo2)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (swvr-accessor memo1 swvr-x swvr-n)))))

(defun-sk swvr-cmap-eq-0072 (swvr-v-t memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (if (equal swvr-x swvr-v-t) (swvr-black-some 0) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0073 (p swvr-v-t memo1 memo2)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (if (equal swvr-x swvr-v-t) (if (equal swvr-n 0) p (swvr-accessor memo1 swvr-v-t swvr-n)) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0074 (memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (swvr-colors memo1 swvr-x)))))

(defun-sk swvr-amap-eq-0075 (p swvr-v-t memo1 memo2 m)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (if (equal swvr-x p) (if (equal swvr-n m) swvr-v-t (swvr-accessor memo1 p swvr-n)) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0076 (p memo1 memo2 n)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (if (equal swvr-x p) (swvr-black-some n) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0077 (p swvr-v-t memo1 memo2 m n)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (if (equal swvr-x p) (if (equal swvr-n m) swvr-v-t (if (equal swvr-n n) (swvr-accessor memo1 p m) (swvr-accessor memo1 p swvr-n))) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun swvr-forall-0078-body (memo1 s p1 memo2 j)
  (implies (and (integerp j)) (implies (and (and (<= 0 j) (< j s)) (not (equal j 0))) (equal (swvr-accessor memo2 p1 j) (swvr-accessor memo1 p1 j)))))

(defun-sk swvr-forall-0078 (memo1 s p1 memo2)
  (forall (j)
    (swvr-forall-0078-body memo1 s p1 memo2 j)))

(defun swvr-forall-0079-body (memo1 p1 memo2 l n)
  (implies (and (swvr-loc-p l) (integerp n)) (implies (and (not (equal l (swvr-null))) (not (equal l p1)) (<= 0 n) (< n (swvr-block-size memo2 l))) (equal (swvr-accessor memo2 l n) (swvr-accessor memo1 l n)))))

(defun-sk swvr-forall-0079 (memo1 p1 memo2)
  (forall (l n)
    (swvr-forall-0079-body memo1 p1 memo2 l n)))

(defun swvr-forall-0080-body (p1 memo2 j)
  (implies (and (integerp j)) (implies (and (<= 0 j) (< j 0)) (let ((l (swvr-accessor memo2 p1 j))) (or (equal l (swvr-null)) (swvr-black-p (swvr-colors memo2 l)))))))

(defun-sk swvr-forall-0080 (p1 memo2)
  (forall (j)
    (swvr-forall-0080-body p1 memo2 j)))

(defun swvr-forall-0081-body (memo memo1 p1 memo2 l)
  (implies (and (swvr-loc-p l)) (implies (not (equal l (swvr-null))) (implies (or (not (swvr-path-p memo p1 l)) (swvr-black-p (swvr-colors memo1 l))) (equal (swvr-colors memo2 l) (swvr-colors memo1 l))))))

(defun-sk swvr-forall-0081 (memo memo1 p1 memo2)
  (forall (l)
    (swvr-forall-0081-body memo memo1 p1 memo2 l)))

(defun-sk swvr-bmap-eq-0082 (memo2 memo3)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo3 swvr-x) (swvr-block-size memo2 swvr-x)))))

(defun swvr-forall-0083-body (memo1 s p2 memo3 i j)
  (implies (and (integerp j)) (implies (and (and (<= 0 j) (< j s)) (not (equal j i))) (equal (swvr-accessor memo3 p2 j) (swvr-accessor memo1 p2 j)))))

(defun-sk swvr-forall-0083 (memo1 s p2 memo3 i)
  (forall (j)
    (swvr-forall-0083-body memo1 s p2 memo3 i j)))

(defun swvr-forall-0084-body (memo1 p2 memo3 l n)
  (implies (and (swvr-loc-p l) (integerp n)) (implies (and (not (equal l (swvr-null))) (not (equal l p2)) (<= 0 n) (< n (swvr-block-size memo3 l))) (equal (swvr-accessor memo3 l n) (swvr-accessor memo1 l n)))))

(defun-sk swvr-forall-0084 (memo1 p2 memo3)
  (forall (l n)
    (swvr-forall-0084-body memo1 p2 memo3 l n)))

(defun swvr-forall-0085-body (p2 memo3 i j)
  (implies (and (integerp j)) (implies (and (<= 0 j) (< j i)) (let ((l (swvr-accessor memo3 p2 j))) (or (equal l (swvr-null)) (swvr-black-p (swvr-colors memo3 l)))))))

(defun-sk swvr-forall-0085 (p2 memo3 i)
  (forall (j)
    (swvr-forall-0085-body p2 memo3 i j)))

(defun swvr-forall-0086-body (memo memo1 p2 memo3 l)
  (implies (and (swvr-loc-p l)) (implies (not (equal l (swvr-null))) (implies (or (not (swvr-path-p memo p2 l)) (swvr-black-p (swvr-colors memo1 l))) (equal (swvr-colors memo3 l) (swvr-colors memo1 l))))))

(defun-sk swvr-forall-0086 (memo memo1 p2 memo3)
  (forall (l)
    (swvr-forall-0086-body memo memo1 p2 memo3 l)))

(defun swvr-forall-0087-body (memo memo3 x n)
  (implies (and (swvr-loc-p x) (integerp n)) (implies (and (not (equal x (swvr-null))) (not (swvr-black-p (swvr-colors memo3 x))) (<= 0 n) (< n (swvr-block-size memo3 x))) (equal (swvr-accessor memo3 x n) (swvr-accessor memo x n)))))

(defun-sk swvr-forall-0087 (memo memo3)
  (forall (x n)
    (swvr-forall-0087-body memo memo3 x n)))

(defun-sk swvr-bmap-eq-0088 (memo3 memo4)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo4 swvr-x) (swvr-block-size memo3 swvr-x)))))

(defun swvr-forall-0089-body (memo t2 memo3 memo4 x)
  (implies (and (swvr-loc-p x)) (implies (not (equal x (swvr-null))) (implies (or (not (swvr-path-p memo t2 x)) (swvr-black-p (swvr-colors memo3 x))) (equal (swvr-colors memo4 x) (swvr-colors memo3 x))))))

(defun-sk swvr-forall-0089 (memo t2 memo3 memo4)
  (forall (x)
    (swvr-forall-0089-body memo t2 memo3 memo4 x)))

(defun-sk swvr-bmap-eq-0090 (memo4 memo5)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo5 swvr-x) (swvr-block-size memo4 swvr-x)))))

(defun-sk swvr-cmap-eq-0091 (t2 memo4 memo5)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo5 swvr-x) (if (equal swvr-x t2) (swvr-black-none) (swvr-colors memo4 swvr-x))))))

(defun-sk swvr-amap-eq-0092 (memo4 memo5)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo5 swvr-x swvr-n) (swvr-accessor memo4 swvr-x swvr-n)))))

(defun-sk swvr-cmap-eq-0093 (t2 memo4 memo5)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo5 swvr-x) (if (equal swvr-x t2) (swvr-black-some 0) (swvr-colors memo4 swvr-x))))))

(defun-sk swvr-amap-eq-0094 (p2 t2 memo4 memo5)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo5 swvr-x swvr-n) (if (equal swvr-x t2) (if (equal swvr-n 0) p2 (swvr-accessor memo4 t2 swvr-n)) (swvr-accessor memo4 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0095 (memo4 memo5)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo5 swvr-x) (swvr-colors memo4 swvr-x)))))

(defun-sk swvr-amap-eq-0096 (p2 t2 memo4 memo5 m)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo5 swvr-x swvr-n) (if (equal swvr-x p2) (if (equal swvr-n m) t2 (swvr-accessor memo4 p2 swvr-n)) (swvr-accessor memo4 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0097 (p2 memo4 memo5 n)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo5 swvr-x) (if (equal swvr-x p2) (swvr-black-some n) (swvr-colors memo4 swvr-x))))))

(defun-sk swvr-amap-eq-0098 (p2 t2 memo4 memo5 m n)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo5 swvr-x swvr-n) (if (equal swvr-x p2) (if (equal swvr-n m) t2 (if (equal swvr-n n) (swvr-accessor memo4 p2 m) (swvr-accessor memo4 p2 swvr-n))) (swvr-accessor memo4 swvr-x swvr-n))))))

(defun swvr-forall-0099-body (memo1 s i p3 memo5 j)
  (implies (and (integerp j)) (implies (and (and (<= 0 j) (< j s)) (not (equal j (+ i 1)))) (equal (swvr-accessor memo5 p3 j) (swvr-accessor memo1 p3 j)))))

(defun-sk swvr-forall-0099 (memo1 s i p3 memo5)
  (forall (j)
    (swvr-forall-0099-body memo1 s i p3 memo5 j)))

(defun swvr-forall-0100-body (memo1 p3 memo5 l n)
  (implies (and (swvr-loc-p l) (integerp n)) (implies (and (not (equal l (swvr-null))) (not (equal l p3)) (<= 0 n) (< n (swvr-block-size memo5 l))) (equal (swvr-accessor memo5 l n) (swvr-accessor memo1 l n)))))

(defun-sk swvr-forall-0100 (memo1 p3 memo5)
  (forall (l n)
    (swvr-forall-0100-body memo1 p3 memo5 l n)))

(defun swvr-forall-0101-body (i p3 memo5 j)
  (implies (and (integerp j)) (implies (and (<= 0 j) (< j (+ i 1))) (let ((l (swvr-accessor memo5 p3 j))) (or (equal l (swvr-null)) (swvr-black-p (swvr-colors memo5 l)))))))

(defun-sk swvr-forall-0101 (i p3 memo5)
  (forall (j)
    (swvr-forall-0101-body i p3 memo5 j)))

(defun swvr-forall-0102-body (memo memo1 p3 memo5 l)
  (implies (and (swvr-loc-p l)) (implies (not (equal l (swvr-null))) (implies (or (not (swvr-path-p memo p3 l)) (swvr-black-p (swvr-colors memo1 l))) (equal (swvr-colors memo5 l) (swvr-colors memo1 l))))))

(defun-sk swvr-forall-0102 (memo memo1 p3 memo5)
  (forall (l)
    (swvr-forall-0102-body memo memo1 p3 memo5 l)))

(defun-sk swvr-cmap-eq-0103 (memo4 memo5)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo5 swvr-x) (swvr-colors memo4 swvr-x)))))

(defun-sk swvr-amap-eq-0104 (memo4 memo5)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo5 swvr-x swvr-n) (swvr-accessor memo4 swvr-x swvr-n)))))

(defun swvr-forall-0105-body (graph memo p swvr-v-t memo1 s g2 p2 t2 i memo4 p3 t3 memo5)
  (implies (and (swvr-loc-p p3) (swvr-loc-p t3) (swvr-memory-p memo5)) (implies (swvr-bmap-eq-0090 memo4 memo5) (and (implies (and (or (not (equal p2 (swvr-null))) (and (not (equal t2 (swvr-null))) (not (swvr-black-p (swvr-colors memo4 t2))))) (implies (and (not (equal t2 (swvr-null))) (not (swvr-black-p (swvr-colors memo4 t2))) (equal (swvr-block-size memo4 t2) 0)) (and (swvr-cmap-eq-0091 t2 memo4 memo5) (equal t3 t2) (equal p3 p2) (swvr-amap-eq-0092 memo4 memo5))) (implies (and (not (equal t2 (swvr-null))) (not (swvr-black-p (swvr-colors memo4 t2))) (< 0 (swvr-block-size memo4 t2))) (and (swvr-cmap-eq-0093 t2 memo4 memo5) (equal t3 (swvr-accessor memo4 t2 0)) (equal p3 t2) (swvr-amap-eq-0094 p2 t2 memo4 memo5))) (implies (or (equal t2 (swvr-null)) (swvr-black-p (swvr-colors memo4 t2))) (if (swvr-black-some-p (swvr-colors memo4 p2)) (let ((m (swvr-black-index (swvr-colors memo4 p2)))) (let ((n (+ m 1))) (if (equal n (swvr-block-size memo4 p2)) (and (equal t3 p2) (equal p3 (swvr-accessor memo4 p2 m)) (swvr-cmap-eq-0095 memo4 memo5) (swvr-amap-eq-0096 p2 t2 memo4 memo5 m)) (and (equal p3 p2) (equal t3 (swvr-accessor memo4 p2 n)) (swvr-cmap-eq-0097 p2 memo4 memo5 n) (swvr-amap-eq-0098 p2 t2 memo4 memo5 m n))))) nil))) (and (swvr-well-colored-on-p graph g2 memo memo5) (equal p3 swvr-v-t) (equal t3 (swvr-accessor memo p3 (+ i 1))) (equal (swvr-colors memo5 p3) (swvr-black-some (+ i 1))) (swvr-forall-0099 memo1 s i p3 memo5) (equal (swvr-accessor memo5 p3 (+ i 1)) p) (swvr-forall-0100 memo1 p3 memo5) (swvr-forall-0101 i p3 memo5) (swvr-forall-0102 memo memo1 p3 memo5))) (not (and (and (equal p2 (swvr-null)) (or (equal t2 (swvr-null)) (swvr-black-p (swvr-colors memo4 t2)))) (swvr-cmap-eq-0103 memo4 memo5) (swvr-amap-eq-0104 memo4 memo5)))))))

(defun-sk swvr-forall-0105 (graph memo p swvr-v-t memo1 s g2 p2 t2 i memo4)
  (forall (p3 t3 memo5)
    (swvr-forall-0105-body graph memo p swvr-v-t memo1 s g2 p2 t2 i memo4 p3 t3 memo5)))

(defun swvr-forall-0106-body (graph memo p swvr-v-t memo1 s g2 p2 t2 memo3 i memo4)
  (implies (and (swvr-memory-p memo4)) (implies (swvr-bmap-eq-0088 memo3 memo4) (implies (and (swvr-unchanged-p memo3 memo4) (swvr-well-colored-on-p graph g2 memo memo4) (or (swvr-black-p (swvr-colors memo4 t2)) (equal t2 (swvr-null))) (swvr-forall-0089 memo t2 memo3 memo4)) (and (implies (and (not (equal p2 (swvr-null))) (or (equal t2 (swvr-null)) (swvr-black-p (swvr-colors memo4 t2)))) (if (swvr-black-some-p (swvr-colors memo4 p2)) (let ((m (swvr-black-index (swvr-colors memo4 p2)))) (and (<= 0 m) (< m (swvr-block-size memo4 p2)))) nil)) (swvr-forall-0105 graph memo p swvr-v-t memo1 s g2 p2 t2 i memo4))))))

(defun-sk swvr-forall-0106 (graph memo p swvr-v-t memo1 s g2 p2 t2 memo3 i)
  (forall (memo4)
    (swvr-forall-0106-body graph memo p swvr-v-t memo1 s g2 p2 t2 memo3 i memo4)))

(defun swvr-forall-0107-body (graph memo p swvr-v-t memo1 gray s g2 o2 p2 t2 memo3 i)
  (implies (and (integerp i)) (implies (and (and (<= 0 i) (<= i o2)) (swvr-well-colored-on-p graph g2 memo memo3) (equal p2 swvr-v-t) (equal t2 (swvr-accessor memo p2 i)) (equal (swvr-colors memo3 p2) (swvr-black-some i)) (swvr-forall-0083 memo1 s p2 memo3 i) (equal (swvr-accessor memo3 p2 i) p) (swvr-forall-0084 memo1 p2 memo3) (swvr-forall-0085 p2 memo3 i) (swvr-forall-0086 memo memo1 p2 memo3)) (and (and (and (<= 0 (- (len graph) (len gray))) (< (- (len graph) (len g2)) (- (len graph) (len gray)))) (swvr-well-colored-on-p graph g2 memo memo3) (member-equal t2 graph) (swvr-forall-0087 memo memo3)) (swvr-forall-0106 graph memo p swvr-v-t memo1 s g2 p2 t2 memo3 i)))))

(defun-sk swvr-forall-0107 (graph memo p swvr-v-t memo1 gray s g2 o2 p2 t2 memo3)
  (forall (i)
    (swvr-forall-0107-body graph memo p swvr-v-t memo1 gray s g2 o2 p2 t2 memo3 i)))

(defun swvr-forall-0108-body (memo1 s o2 p2 memo3 j)
  (implies (and (integerp j)) (implies (and (and (<= 0 j) (< j s)) (not (equal j (+ o2 1)))) (equal (swvr-accessor memo3 p2 j) (swvr-accessor memo1 p2 j)))))

(defun-sk swvr-forall-0108 (memo1 s o2 p2 memo3)
  (forall (j)
    (swvr-forall-0108-body memo1 s o2 p2 memo3 j)))

(defun swvr-forall-0109-body (memo1 p2 memo3 l n)
  (implies (and (swvr-loc-p l) (integerp n)) (implies (and (not (equal l (swvr-null))) (not (equal l p2)) (<= 0 n) (< n (swvr-block-size memo3 l))) (equal (swvr-accessor memo3 l n) (swvr-accessor memo1 l n)))))

(defun-sk swvr-forall-0109 (memo1 p2 memo3)
  (forall (l n)
    (swvr-forall-0109-body memo1 p2 memo3 l n)))

(defun swvr-forall-0110-body (o2 p2 memo3 j)
  (implies (and (integerp j)) (implies (and (<= 0 j) (< j (+ o2 1))) (let ((l (swvr-accessor memo3 p2 j))) (or (equal l (swvr-null)) (swvr-black-p (swvr-colors memo3 l)))))))

(defun-sk swvr-forall-0110 (o2 p2 memo3)
  (forall (j)
    (swvr-forall-0110-body o2 p2 memo3 j)))

(defun swvr-forall-0111-body (memo memo1 p2 memo3 l)
  (implies (and (swvr-loc-p l)) (implies (not (equal l (swvr-null))) (implies (or (not (swvr-path-p memo p2 l)) (swvr-black-p (swvr-colors memo1 l))) (equal (swvr-colors memo3 l) (swvr-colors memo1 l))))))

(defun-sk swvr-forall-0111 (memo memo1 p2 memo3)
  (forall (l)
    (swvr-forall-0111-body memo memo1 p2 memo3 l)))

(defun swvr-forall-0112-body (memo memo3 x n)
  (implies (and (swvr-loc-p x) (integerp n)) (implies (and (not (equal x (swvr-null))) (not (swvr-black-p (swvr-colors memo3 x))) (<= 0 n) (< n (swvr-block-size memo3 x))) (equal (swvr-accessor memo3 x n) (swvr-accessor memo x n)))))

(defun-sk swvr-forall-0112 (memo memo3)
  (forall (x n)
    (swvr-forall-0112-body memo memo3 x n)))

(defun-sk swvr-bmap-eq-0113 (memo3 memo4)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo4 swvr-x) (swvr-block-size memo3 swvr-x)))))

(defun swvr-forall-0114-body (memo t2 memo3 memo4 x)
  (implies (and (swvr-loc-p x)) (implies (not (equal x (swvr-null))) (implies (or (not (swvr-path-p memo t2 x)) (swvr-black-p (swvr-colors memo3 x))) (equal (swvr-colors memo4 x) (swvr-colors memo3 x))))))

(defun-sk swvr-forall-0114 (memo t2 memo3 memo4)
  (forall (x)
    (swvr-forall-0114-body memo t2 memo3 memo4 x)))

(defun-sk swvr-bmap-eq-0115 (memo4 memo5)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo5 swvr-x) (swvr-block-size memo4 swvr-x)))))

(defun-sk swvr-cmap-eq-0116 (t2 memo4 memo5)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo5 swvr-x) (if (equal swvr-x t2) (swvr-black-none) (swvr-colors memo4 swvr-x))))))

(defun-sk swvr-amap-eq-0117 (memo4 memo5)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo5 swvr-x swvr-n) (swvr-accessor memo4 swvr-x swvr-n)))))

(defun-sk swvr-cmap-eq-0118 (t2 memo4 memo5)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo5 swvr-x) (if (equal swvr-x t2) (swvr-black-some 0) (swvr-colors memo4 swvr-x))))))

(defun-sk swvr-amap-eq-0119 (p2 t2 memo4 memo5)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo5 swvr-x swvr-n) (if (equal swvr-x t2) (if (equal swvr-n 0) p2 (swvr-accessor memo4 t2 swvr-n)) (swvr-accessor memo4 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0120 (memo4 memo5)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo5 swvr-x) (swvr-colors memo4 swvr-x)))))

(defun-sk swvr-amap-eq-0121 (p2 t2 memo4 memo5 m)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo5 swvr-x swvr-n) (if (equal swvr-x p2) (if (equal swvr-n m) t2 (swvr-accessor memo4 p2 swvr-n)) (swvr-accessor memo4 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0122 (p2 memo4 memo5 n)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo5 swvr-x) (if (equal swvr-x p2) (swvr-black-some n) (swvr-colors memo4 swvr-x))))))

(defun-sk swvr-amap-eq-0123 (p2 t2 memo4 memo5 m n)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo5 swvr-x swvr-n) (if (equal swvr-x p2) (if (equal swvr-n m) t2 (if (equal swvr-n n) (swvr-accessor memo4 p2 m) (swvr-accessor memo4 p2 swvr-n))) (swvr-accessor memo4 swvr-x swvr-n))))))

(defun swvr-forall-0124-body (memo memo1 t3 memo5 x)
  (implies (and (swvr-loc-p x)) (implies (not (equal x (swvr-null))) (implies (or (not (swvr-path-p memo t3 x)) (swvr-black-p (swvr-colors memo1 x))) (equal (swvr-colors memo5 x) (swvr-colors memo1 x))))))

(defun-sk swvr-forall-0124 (memo memo1 t3 memo5)
  (forall (x)
    (swvr-forall-0124-body memo memo1 t3 memo5 x)))

(defun-sk swvr-cmap-eq-0125 (memo4 memo5)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo5 swvr-x) (swvr-colors memo4 swvr-x)))))

(defun-sk swvr-amap-eq-0126 (memo4 memo5)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo5 swvr-x swvr-n) (swvr-accessor memo4 swvr-x swvr-n)))))

(defun swvr-forall-0127-body (graph memo p swvr-v-t memo1 gray p2 t2 memo4 p3 t3 memo5)
  (implies (and (swvr-loc-p p3) (swvr-loc-p t3) (swvr-memory-p memo5)) (implies (swvr-bmap-eq-0115 memo4 memo5) (and (implies (and (or (not (equal p2 (swvr-null))) (and (not (equal t2 (swvr-null))) (not (swvr-black-p (swvr-colors memo4 t2))))) (implies (and (not (equal t2 (swvr-null))) (not (swvr-black-p (swvr-colors memo4 t2))) (equal (swvr-block-size memo4 t2) 0)) (and (swvr-cmap-eq-0116 t2 memo4 memo5) (equal t3 t2) (equal p3 p2) (swvr-amap-eq-0117 memo4 memo5))) (implies (and (not (equal t2 (swvr-null))) (not (swvr-black-p (swvr-colors memo4 t2))) (< 0 (swvr-block-size memo4 t2))) (and (swvr-cmap-eq-0118 t2 memo4 memo5) (equal t3 (swvr-accessor memo4 t2 0)) (equal p3 t2) (swvr-amap-eq-0119 p2 t2 memo4 memo5))) (implies (or (equal t2 (swvr-null)) (swvr-black-p (swvr-colors memo4 t2))) (if (swvr-black-some-p (swvr-colors memo4 p2)) (let ((m (swvr-black-index (swvr-colors memo4 p2)))) (let ((n (+ m 1))) (if (equal n (swvr-block-size memo4 p2)) (and (equal t3 p2) (equal p3 (swvr-accessor memo4 p2 m)) (swvr-cmap-eq-0120 memo4 memo5) (swvr-amap-eq-0121 p2 t2 memo4 memo5 m)) (and (equal p3 p2) (equal t3 (swvr-accessor memo4 p2 n)) (swvr-cmap-eq-0122 p2 memo4 memo5 n) (swvr-amap-eq-0123 p2 t2 memo4 memo5 m n))))) nil))) (and (and (equal t3 swvr-v-t) (equal p3 p)) (swvr-unchanged-p memo1 memo5) (swvr-well-colored-on-p graph gray memo memo5) (or (swvr-black-p (swvr-colors memo5 t3)) (equal t3 (swvr-null))) (swvr-forall-0124 memo memo1 t3 memo5))) (not (and (and (equal p2 (swvr-null)) (or (equal t2 (swvr-null)) (swvr-black-p (swvr-colors memo4 t2)))) (swvr-cmap-eq-0125 memo4 memo5) (swvr-amap-eq-0126 memo4 memo5)))))))

(defun-sk swvr-forall-0127 (graph memo p swvr-v-t memo1 gray p2 t2 memo4)
  (forall (p3 t3 memo5)
    (swvr-forall-0127-body graph memo p swvr-v-t memo1 gray p2 t2 memo4 p3 t3 memo5)))

(defun swvr-forall-0128-body (graph memo p swvr-v-t memo1 gray g2 p2 t2 memo3 memo4)
  (implies (and (swvr-memory-p memo4)) (implies (swvr-bmap-eq-0113 memo3 memo4) (implies (and (swvr-unchanged-p memo3 memo4) (swvr-well-colored-on-p graph g2 memo memo4) (or (swvr-black-p (swvr-colors memo4 t2)) (equal t2 (swvr-null))) (swvr-forall-0114 memo t2 memo3 memo4)) (and (implies (and (not (equal p2 (swvr-null))) (or (equal t2 (swvr-null)) (swvr-black-p (swvr-colors memo4 t2)))) (if (swvr-black-some-p (swvr-colors memo4 p2)) (let ((m (swvr-black-index (swvr-colors memo4 p2)))) (and (<= 0 m) (< m (swvr-block-size memo4 p2)))) nil)) (swvr-forall-0127 graph memo p swvr-v-t memo1 gray p2 t2 memo4))))))

(defun-sk swvr-forall-0128 (graph memo p swvr-v-t memo1 gray g2 p2 t2 memo3)
  (forall (memo4)
    (swvr-forall-0128-body graph memo p swvr-v-t memo1 gray g2 p2 t2 memo3 memo4)))

(defun swvr-forall-0129-body (graph memo p swvr-v-t memo1 gray s g2 memo2 o2 p2 t2 memo3)
  (implies (and (swvr-loc-p p2) (swvr-loc-p t2) (swvr-memory-p memo3)) (implies (swvr-bmap-eq-0082 memo2 memo3) (and (swvr-forall-0107 graph memo p swvr-v-t memo1 gray s g2 o2 p2 t2 memo3) (implies (and (swvr-well-colored-on-p graph g2 memo memo3) (equal p2 swvr-v-t) (equal t2 (swvr-accessor memo p2 (+ o2 1))) (equal (swvr-colors memo3 p2) (swvr-black-some (+ o2 1))) (swvr-forall-0108 memo1 s o2 p2 memo3) (equal (swvr-accessor memo3 p2 (+ o2 1)) p) (swvr-forall-0109 memo1 p2 memo3) (swvr-forall-0110 o2 p2 memo3) (swvr-forall-0111 memo memo1 p2 memo3)) (and (and (and (<= 0 (- (len graph) (len gray))) (< (- (len graph) (len g2)) (- (len graph) (len gray)))) (swvr-well-colored-on-p graph g2 memo memo3) (member-equal t2 graph) (swvr-forall-0112 memo memo3)) (swvr-forall-0128 graph memo p swvr-v-t memo1 gray g2 p2 t2 memo3)))))))

(defun-sk swvr-forall-0129 (graph memo p swvr-v-t memo1 gray s g2 memo2 o2)
  (forall (p2 t2 memo3)
    (swvr-forall-0129-body graph memo p swvr-v-t memo1 gray s g2 memo2 o2 p2 t2 memo3)))

(defun swvr-forall-0130-body (memo memo2 x n)
  (implies (and (swvr-loc-p x) (integerp n)) (implies (and (not (equal x (swvr-null))) (not (swvr-black-p (swvr-colors memo2 x))) (<= 0 n) (< n (swvr-block-size memo2 x))) (equal (swvr-accessor memo2 x n) (swvr-accessor memo x n)))))

(defun-sk swvr-forall-0130 (memo memo2)
  (forall (x n)
    (swvr-forall-0130-body memo memo2 x n)))

(defun-sk swvr-bmap-eq-0131 (memo2 memo3)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo3 swvr-x) (swvr-block-size memo2 swvr-x)))))

(defun swvr-forall-0132-body (memo t1 memo2 memo3 x)
  (implies (and (swvr-loc-p x)) (implies (not (equal x (swvr-null))) (implies (or (not (swvr-path-p memo t1 x)) (swvr-black-p (swvr-colors memo2 x))) (equal (swvr-colors memo3 x) (swvr-colors memo2 x))))))

(defun-sk swvr-forall-0132 (memo t1 memo2 memo3)
  (forall (x)
    (swvr-forall-0132-body memo t1 memo2 memo3 x)))

(defun-sk swvr-bmap-eq-0133 (memo3 memo4)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo4 swvr-x) (swvr-block-size memo3 swvr-x)))))

(defun-sk swvr-cmap-eq-0134 (t1 memo3 memo4)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo4 swvr-x) (if (equal swvr-x t1) (swvr-black-none) (swvr-colors memo3 swvr-x))))))

(defun-sk swvr-amap-eq-0135 (memo3 memo4)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo4 swvr-x swvr-n) (swvr-accessor memo3 swvr-x swvr-n)))))

(defun-sk swvr-cmap-eq-0136 (t1 memo3 memo4)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo4 swvr-x) (if (equal swvr-x t1) (swvr-black-some 0) (swvr-colors memo3 swvr-x))))))

(defun-sk swvr-amap-eq-0137 (p1 t1 memo3 memo4)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo4 swvr-x swvr-n) (if (equal swvr-x t1) (if (equal swvr-n 0) p1 (swvr-accessor memo3 t1 swvr-n)) (swvr-accessor memo3 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0138 (memo3 memo4)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo4 swvr-x) (swvr-colors memo3 swvr-x)))))

(defun-sk swvr-amap-eq-0139 (p1 t1 memo3 memo4 m)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo4 swvr-x swvr-n) (if (equal swvr-x p1) (if (equal swvr-n m) t1 (swvr-accessor memo3 p1 swvr-n)) (swvr-accessor memo3 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0140 (p1 memo3 memo4 n)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo4 swvr-x) (if (equal swvr-x p1) (swvr-black-some n) (swvr-colors memo3 swvr-x))))))

(defun-sk swvr-amap-eq-0141 (p1 t1 memo3 memo4 m n)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo4 swvr-x swvr-n) (if (equal swvr-x p1) (if (equal swvr-n m) t1 (if (equal swvr-n n) (swvr-accessor memo3 p1 m) (swvr-accessor memo3 p1 swvr-n))) (swvr-accessor memo3 swvr-x swvr-n))))))

(defun swvr-forall-0142-body (memo memo1 t2 memo4 x)
  (implies (and (swvr-loc-p x)) (implies (not (equal x (swvr-null))) (implies (or (not (swvr-path-p memo t2 x)) (swvr-black-p (swvr-colors memo1 x))) (equal (swvr-colors memo4 x) (swvr-colors memo1 x))))))

(defun-sk swvr-forall-0142 (memo memo1 t2 memo4)
  (forall (x)
    (swvr-forall-0142-body memo memo1 t2 memo4 x)))

(defun-sk swvr-cmap-eq-0143 (memo3 memo4)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo4 swvr-x) (swvr-colors memo3 swvr-x)))))

(defun-sk swvr-amap-eq-0144 (memo3 memo4)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo4 swvr-x swvr-n) (swvr-accessor memo3 swvr-x swvr-n)))))

(defun swvr-forall-0145-body (graph memo p swvr-v-t memo1 gray p1 t1 memo3 p2 t2 memo4)
  (implies (and (swvr-loc-p p2) (swvr-loc-p t2) (swvr-memory-p memo4)) (implies (swvr-bmap-eq-0133 memo3 memo4) (and (implies (and (or (not (equal p1 (swvr-null))) (and (not (equal t1 (swvr-null))) (not (swvr-black-p (swvr-colors memo3 t1))))) (implies (and (not (equal t1 (swvr-null))) (not (swvr-black-p (swvr-colors memo3 t1))) (equal (swvr-block-size memo3 t1) 0)) (and (swvr-cmap-eq-0134 t1 memo3 memo4) (equal t2 t1) (equal p2 p1) (swvr-amap-eq-0135 memo3 memo4))) (implies (and (not (equal t1 (swvr-null))) (not (swvr-black-p (swvr-colors memo3 t1))) (< 0 (swvr-block-size memo3 t1))) (and (swvr-cmap-eq-0136 t1 memo3 memo4) (equal t2 (swvr-accessor memo3 t1 0)) (equal p2 t1) (swvr-amap-eq-0137 p1 t1 memo3 memo4))) (implies (or (equal t1 (swvr-null)) (swvr-black-p (swvr-colors memo3 t1))) (if (swvr-black-some-p (swvr-colors memo3 p1)) (let ((m (swvr-black-index (swvr-colors memo3 p1)))) (let ((n (+ m 1))) (if (equal n (swvr-block-size memo3 p1)) (and (equal t2 p1) (equal p2 (swvr-accessor memo3 p1 m)) (swvr-cmap-eq-0138 memo3 memo4) (swvr-amap-eq-0139 p1 t1 memo3 memo4 m)) (and (equal p2 p1) (equal t2 (swvr-accessor memo3 p1 n)) (swvr-cmap-eq-0140 p1 memo3 memo4 n) (swvr-amap-eq-0141 p1 t1 memo3 memo4 m n))))) nil))) (and (and (equal t2 swvr-v-t) (equal p2 p)) (swvr-unchanged-p memo1 memo4) (swvr-well-colored-on-p graph gray memo memo4) (or (swvr-black-p (swvr-colors memo4 t2)) (equal t2 (swvr-null))) (swvr-forall-0142 memo memo1 t2 memo4))) (not (and (and (equal p1 (swvr-null)) (or (equal t1 (swvr-null)) (swvr-black-p (swvr-colors memo3 t1)))) (swvr-cmap-eq-0143 memo3 memo4) (swvr-amap-eq-0144 memo3 memo4)))))))

(defun-sk swvr-forall-0145 (graph memo p swvr-v-t memo1 gray p1 t1 memo3)
  (forall (p2 t2 memo4)
    (swvr-forall-0145-body graph memo p swvr-v-t memo1 gray p1 t1 memo3 p2 t2 memo4)))

(defun swvr-forall-0146-body (graph memo p swvr-v-t memo1 gray g2 p1 t1 memo2 memo3)
  (implies (and (swvr-memory-p memo3)) (implies (swvr-bmap-eq-0131 memo2 memo3) (implies (and (swvr-unchanged-p memo2 memo3) (swvr-well-colored-on-p graph g2 memo memo3) (or (swvr-black-p (swvr-colors memo3 t1)) (equal t1 (swvr-null))) (swvr-forall-0132 memo t1 memo2 memo3)) (and (implies (and (not (equal p1 (swvr-null))) (or (equal t1 (swvr-null)) (swvr-black-p (swvr-colors memo3 t1)))) (if (swvr-black-some-p (swvr-colors memo3 p1)) (let ((m (swvr-black-index (swvr-colors memo3 p1)))) (and (<= 0 m) (< m (swvr-block-size memo3 p1)))) nil)) (swvr-forall-0145 graph memo p swvr-v-t memo1 gray p1 t1 memo3))))))

(defun-sk swvr-forall-0146 (graph memo p swvr-v-t memo1 gray g2 p1 t1 memo2)
  (forall (memo3)
    (swvr-forall-0146-body graph memo p swvr-v-t memo1 gray g2 p1 t1 memo2 memo3)))

(defun swvr-forall-0147-body (memo memo1 t1 memo2 x)
  (implies (and (swvr-loc-p x)) (implies (not (equal x (swvr-null))) (implies (or (not (swvr-path-p memo t1 x)) (swvr-black-p (swvr-colors memo1 x))) (equal (swvr-colors memo2 x) (swvr-colors memo1 x))))))

(defun-sk swvr-forall-0147 (memo memo1 t1 memo2)
  (forall (x)
    (swvr-forall-0147-body memo memo1 t1 memo2 x)))

(defun-sk swvr-cmap-eq-0148 (memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (swvr-colors memo1 swvr-x)))))

(defun-sk swvr-amap-eq-0149 (memo1 memo2)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (swvr-accessor memo1 swvr-x swvr-n)))))

(defun swvr-forall-0150-body (graph memo p swvr-v-t memo1 gray s g2 p1 t1 memo2)
  (implies (and (swvr-loc-p p1) (swvr-loc-p t1) (swvr-memory-p memo2)) (implies (swvr-bmap-eq-0069 memo1 memo2) (and (implies (and (or (not (equal p (swvr-null))) (and (not (equal swvr-v-t (swvr-null))) (not (swvr-black-p (swvr-colors memo1 swvr-v-t))))) (implies (and (not (equal swvr-v-t (swvr-null))) (not (swvr-black-p (swvr-colors memo1 swvr-v-t))) (equal (swvr-block-size memo1 swvr-v-t) 0)) (and (swvr-cmap-eq-0070 swvr-v-t memo1 memo2) (equal t1 swvr-v-t) (equal p1 p) (swvr-amap-eq-0071 memo1 memo2))) (implies (and (not (equal swvr-v-t (swvr-null))) (not (swvr-black-p (swvr-colors memo1 swvr-v-t))) (< 0 (swvr-block-size memo1 swvr-v-t))) (and (swvr-cmap-eq-0072 swvr-v-t memo1 memo2) (equal t1 (swvr-accessor memo1 swvr-v-t 0)) (equal p1 swvr-v-t) (swvr-amap-eq-0073 p swvr-v-t memo1 memo2))) (implies (or (equal swvr-v-t (swvr-null)) (swvr-black-p (swvr-colors memo1 swvr-v-t))) (if (swvr-black-some-p (swvr-colors memo1 p)) (let ((m (swvr-black-index (swvr-colors memo1 p)))) (let ((n (+ m 1))) (if (equal n (swvr-block-size memo1 p)) (and (equal t1 p) (equal p1 (swvr-accessor memo1 p m)) (swvr-cmap-eq-0074 memo1 memo2) (swvr-amap-eq-0075 p swvr-v-t memo1 memo2 m)) (and (equal p1 p) (equal t1 (swvr-accessor memo1 p n)) (swvr-cmap-eq-0076 p memo1 memo2 n) (swvr-amap-eq-0077 p swvr-v-t memo1 memo2 m n))))) nil))) (if (not (equal s 0)) (let ((o2 (- s 2))) (and (implies (<= 0 (+ o2 1)) (and (and (swvr-well-colored-on-p graph g2 memo memo2) (equal p1 swvr-v-t) (equal t1 (swvr-accessor memo p1 0)) (equal (swvr-colors memo2 p1) (swvr-black-some 0)) (swvr-forall-0078 memo1 s p1 memo2) (equal (swvr-accessor memo2 p1 0) p) (swvr-forall-0079 memo1 p1 memo2) (swvr-forall-0080 p1 memo2) (swvr-forall-0081 memo memo1 p1 memo2)) (swvr-forall-0129 graph memo p swvr-v-t memo1 gray s g2 memo2 o2))) (implies (< (+ o2 1) 0) (and (and (and (<= 0 (- (len graph) (len gray))) (< (- (len graph) (len g2)) (- (len graph) (len gray)))) (swvr-well-colored-on-p graph g2 memo memo2) (member-equal t1 graph) (swvr-forall-0130 memo memo2)) (swvr-forall-0146 graph memo p swvr-v-t memo1 gray g2 p1 t1 memo2))))) (and (and (equal t1 swvr-v-t) (equal p1 p)) (swvr-unchanged-p memo1 memo2) (swvr-well-colored-on-p graph gray memo memo2) (or (swvr-black-p (swvr-colors memo2 t1)) (equal t1 (swvr-null))) (swvr-forall-0147 memo memo1 t1 memo2)))) (not (and (and (equal p (swvr-null)) (or (equal swvr-v-t (swvr-null)) (swvr-black-p (swvr-colors memo1 swvr-v-t)))) (swvr-cmap-eq-0148 memo1 memo2) (swvr-amap-eq-0149 memo1 memo2)))))))

(defun-sk swvr-forall-0150 (graph memo p swvr-v-t memo1 gray s g2)
  (forall (p1 t1 memo2)
    (swvr-forall-0150-body graph memo p swvr-v-t memo1 gray s g2 p1 t1 memo2)))

(defun swvr-forall-0151-body (graph memo p swvr-v-t memo1 gray o1)
  (implies (and (booleanp o1)) (implies (if (equal swvr-v-t (swvr-null)) (equal o1 t) (equal o1 (if (swvr-black-p (swvr-colors memo1 swvr-v-t)) t nil))) (if (equal o1 t) (and (swvr-unchanged-p memo1 memo1) (swvr-well-colored-on-p graph gray memo memo1) (or (swvr-black-p (swvr-colors memo1 swvr-v-t)) (equal swvr-v-t (swvr-null)))) (and (not (equal swvr-v-t (swvr-null))) (let ((s (swvr-block-size memo1 swvr-v-t))) (implies (<= 0 s) (let ((g2 (swvr-fset-insert swvr-v-t gray))) (and (implies (and (not (equal p (swvr-null))) (or (equal swvr-v-t (swvr-null)) (swvr-black-p (swvr-colors memo1 swvr-v-t)))) (if (swvr-black-some-p (swvr-colors memo1 p)) (let ((m (swvr-black-index (swvr-colors memo1 p)))) (and (<= 0 m) (< m (swvr-block-size memo1 p)))) nil)) (swvr-forall-0150 graph memo p swvr-v-t memo1 gray s g2))))))))))

(defun-sk swvr-forall-0151 (graph memo p swvr-v-t memo1 gray)
  (forall (o1)
    (swvr-forall-0151-body graph memo p swvr-v-t memo1 gray o1)))

(defun swvr-forall-0152-body (graph memo p swvr-v-t memo1 gray)
  (implies (and (swvr-loc-fset-p gray)) (implies (and (swvr-well-colored-on-p graph gray memo memo1) (member-equal swvr-v-t graph) (swvr-forall-0068 memo memo1)) (swvr-forall-0151 graph memo p swvr-v-t memo1 gray))))

(defun-sk swvr-forall-0152 (graph memo p swvr-v-t memo1)
  (forall (gray)
    (swvr-forall-0152-body graph memo p swvr-v-t memo1 gray)))

(defun swvr-forall-0153-body (graph memo p swvr-v-t memo1)
  (implies (and (swvr-loc-p p) (swvr-loc-p swvr-v-t) (swvr-memory-p memo1)) (implies (swvr-bmap-eq-0067 memo memo1) (swvr-forall-0152 graph memo p swvr-v-t memo1))))

(defun-sk swvr-forall-0153 (graph memo)
  (forall (p swvr-v-t memo1)
    (swvr-forall-0153-body graph memo p swvr-v-t memo1)))

(defun-sk swvr-bmap-eq-0154 (memo memo1)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo1 swvr-x) (swvr-block-size memo swvr-x)))))

(defun swvr-forall-0155-body (root memo memo1 x)
  (implies (and (swvr-loc-p x)) (implies (not (equal x (swvr-null))) (implies (or (not (swvr-path-p memo root x)) (swvr-black-p (swvr-colors memo x))) (equal (swvr-colors memo1 x) (swvr-colors memo x))))))

(defun-sk swvr-forall-0155 (root memo memo1)
  (forall (x)
    (swvr-forall-0155-body root memo memo1 x)))

(defun-sk swvr-bmap-eq-0156 (memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-block-size memo2 swvr-x) (swvr-block-size memo1 swvr-x)))))

(defun-sk swvr-cmap-eq-0157 (root memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (if (equal swvr-x root) (swvr-black-none) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0158 (memo1 memo2)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (swvr-accessor memo1 swvr-x swvr-n)))))

(defun-sk swvr-cmap-eq-0159 (root memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (if (equal swvr-x root) (swvr-black-some 0) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0160 (root memo1 memo2)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (if (equal swvr-x root) (if (equal swvr-n 0) (swvr-null) (swvr-accessor memo1 root swvr-n)) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0161 (memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (swvr-colors memo1 swvr-x)))))

(defun-sk swvr-amap-eq-0162 (root memo1 memo2 m)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (if (equal swvr-x (swvr-null)) (if (equal swvr-n m) root (swvr-accessor memo1 (swvr-null) swvr-n)) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0163 (memo1 memo2 n)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (if (equal swvr-x (swvr-null)) (swvr-black-some n) (swvr-colors memo1 swvr-x))))))

(defun-sk swvr-amap-eq-0164 (root memo1 memo2 m n)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (if (equal swvr-x (swvr-null)) (if (equal swvr-n m) root (if (equal swvr-n n) (swvr-accessor memo1 (swvr-null) m) (swvr-accessor memo1 (swvr-null) swvr-n))) (swvr-accessor memo1 swvr-x swvr-n))))))

(defun-sk swvr-cmap-eq-0165 (memo1 memo2)
  (forall (swvr-x)
    (implies (and (swvr-loc-p swvr-x))
             (equal (swvr-colors memo2 swvr-x) (swvr-colors memo1 swvr-x)))))

(defun-sk swvr-amap-eq-0166 (memo1 memo2)
  (forall (swvr-x swvr-n)
    (implies (and (swvr-loc-p swvr-x) (integerp swvr-n))
             (equal (swvr-accessor memo2 swvr-x swvr-n) (swvr-accessor memo1 swvr-x swvr-n)))))

(defun swvr-forall-0167-body (root memo memo2 x)
  (implies (and (swvr-loc-p x)) (implies (and (swvr-path-p memo root x) (not (equal x (swvr-null)))) (swvr-black-p (swvr-colors memo2 x)))))

(defun-sk swvr-forall-0167 (root memo memo2)
  (forall (x)
    (swvr-forall-0167-body root memo memo2 x)))

(defun swvr-forall-0168-body (root memo memo2 x)
  (implies (and (swvr-loc-p x)) (implies (and (not (swvr-path-p memo root x)) (not (equal x (swvr-null)))) (equal (swvr-colors memo2 x) (swvr-colors memo x)))))

(defun-sk swvr-forall-0168 (root memo memo2)
  (forall (x)
    (swvr-forall-0168-body root memo memo2 x)))

(defun swvr-forall-0169-body (root memo memo1 p swvr-v-t memo2)
  (implies (and (swvr-loc-p p) (swvr-loc-p swvr-v-t) (swvr-memory-p memo2)) (implies (swvr-bmap-eq-0156 memo1 memo2) (and (not (and (or (not t) (and (not (equal root (swvr-null))) (not (swvr-black-p (swvr-colors memo1 root))))) (implies (and (not (equal root (swvr-null))) (not (swvr-black-p (swvr-colors memo1 root))) (equal (swvr-block-size memo1 root) 0)) (and (swvr-cmap-eq-0157 root memo1 memo2) (equal swvr-v-t root) (equal p (swvr-null)) (swvr-amap-eq-0158 memo1 memo2))) (implies (and (not (equal root (swvr-null))) (not (swvr-black-p (swvr-colors memo1 root))) (< 0 (swvr-block-size memo1 root))) (and (swvr-cmap-eq-0159 root memo1 memo2) (equal swvr-v-t (swvr-accessor memo1 root 0)) (equal p root) (swvr-amap-eq-0160 root memo1 memo2))) (implies (or (equal root (swvr-null)) (swvr-black-p (swvr-colors memo1 root))) (if (swvr-black-some-p (swvr-colors memo1 (swvr-null))) (let ((m (swvr-black-index (swvr-colors memo1 (swvr-null))))) (let ((n (+ m 1))) (if (equal n (swvr-block-size memo1 (swvr-null))) (and (equal swvr-v-t (swvr-null)) (equal p (swvr-accessor memo1 (swvr-null) m)) (swvr-cmap-eq-0161 memo1 memo2) (swvr-amap-eq-0162 root memo1 memo2 m)) (and (equal p (swvr-null)) (equal swvr-v-t (swvr-accessor memo1 (swvr-null) n)) (swvr-cmap-eq-0163 memo1 memo2 n) (swvr-amap-eq-0164 root memo1 memo2 m n))))) nil)))) (implies (and (or (equal root (swvr-null)) (swvr-black-p (swvr-colors memo1 root))) (swvr-cmap-eq-0165 memo1 memo2) (swvr-amap-eq-0166 memo1 memo2)) (and (swvr-unchanged-p memo memo2) (swvr-forall-0167 root memo memo2) (swvr-forall-0168 root memo memo2)))))))

(defun-sk swvr-forall-0169 (root memo memo1)
  (forall (p swvr-v-t memo2)
    (swvr-forall-0169-body root memo memo1 p swvr-v-t memo2)))

(defun swvr-forall-0170-body (root graph memo o1 memo1)
  (implies (and (swvr-memory-p memo1)) (implies (swvr-bmap-eq-0154 memo memo1) (implies (and (swvr-unchanged-p memo memo1) (swvr-well-colored-on-p graph o1 memo memo1) (or (swvr-black-p (swvr-colors memo1 root)) (equal root (swvr-null))) (swvr-forall-0155 root memo memo1)) (and (implies (and (not t) (or (equal root (swvr-null)) (swvr-black-p (swvr-colors memo1 root)))) (if (swvr-black-some-p (swvr-colors memo1 (swvr-null))) (let ((m (swvr-black-index (swvr-colors memo1 (swvr-null))))) (and (<= 0 m) (< m (swvr-block-size memo1 (swvr-null))))) nil)) (swvr-forall-0169 root memo memo1))))))

(defun-sk swvr-forall-0170 (root graph memo o1)
  (forall (memo1)
    (swvr-forall-0170-body root graph memo o1 memo1)))

(defun schorr-waite-via-recursion-statement (root graph memo)
  (implies
   (and (swvr-loc-p (swvr-null))
        (swvr-interface-typed-p)
        (swvr-loc-p root)
        (swvr-loc-fset-p graph)
        (swvr-memory-p memo)
        (member-equal root graph)
        (swvr-forall-0001 graph memo)
        (swvr-forall-0002 graph memo))
   (and (swvr-forall-0066 memo) (swvr-forall-0153 graph memo) (let ((o1 nil)) (and (and (swvr-well-colored-on-p graph o1 memo memo) (member-equal root graph)) (swvr-forall-0170 root graph memo o1))))))

(value-triple :itpeval-statement-checked)
:q
