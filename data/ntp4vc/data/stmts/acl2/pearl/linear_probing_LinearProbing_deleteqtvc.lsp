;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/linear_probing_LinearProbing_deleteqtvc: the deletion loop of a
;; linear-probing table preserves its circular probing and representation
;; obligations across the next bucket and the two array updates. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces represent the two arbitrary source types and the
;; source functions.  Function-typed values such as view and loc remain
;; first-class arguments, with application supplied by the two evaluators.

(defstub lp-delete-key-p (x) t)
(defstub lp-delete-keym-p (x) t)
(defstub lp-delete-key-default () t)
(defstub lp-delete-keym-default () t)
(defstub lp-delete-keym1 (x) t)
(defstub lp-delete-hash (x) t)
(defstub lp-delete-dummy () t)
(defstub lp-delete-view-apply (view keym) t)
(defstub lp-delete-loc-apply (loc keym) t)

(defun lp-delete-eq-p (x y)
  (equal (lp-delete-keym1 x)
         (lp-delete-keym1 y)))

(defun lp-delete-neq-p (x y)
  (not (lp-delete-eq-p x y)))

(defun-sk lp-delete-global-laws-p ()
  (forall (x y)
    (and
     (implies
      (lp-delete-key-p x)
      (and
       (lp-delete-keym-p (lp-delete-keym1 x))
       (integerp (lp-delete-hash x))
       (<= 0 (lp-delete-hash x))))
     (implies
      (and
       (lp-delete-key-p x)
       (lp-delete-key-p y)
       (lp-delete-eq-p x y))
      (equal (lp-delete-hash x)
             (lp-delete-hash y))))))

(defun lp-delete-context-p ()
  (and
   (lp-delete-key-p (lp-delete-key-default))
   (lp-delete-keym-p (lp-delete-keym-default))
   (lp-delete-key-p (lp-delete-dummy))
   (lp-delete-global-laws-p)))

(defun-sk lp-delete-view-function-p (view)
  (forall (m)
    (implies
     (lp-delete-keym-p m)
     (booleanp (lp-delete-view-apply view m)))))

(defun-sk lp-delete-loc-function-p (loc)
  (forall (m)
    (implies
     (lp-delete-keym-p m)
     (integerp (lp-delete-loc-apply loc m)))))

(defun lp-delete-key-list-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (lp-delete-key-p (car a))
       (lp-delete-key-list-p (cdr a)))
    (equal a nil)))

;; INT.TONAT sends a negative integer to zero.  The source's getElem! uses an
;; arbitrary inhabited default outside the list.

(defun lp-delete-nth (i a)
  (if (< (nfix i) (len a))
      (nth (nfix i) a)
    (lp-delete-key-default)))

(defun lp-delete-set-nat (a n value)
  (declare (xargs :measure (acl2-count a)))
  (if (endp a)
      nil
    (if (zp n)
        (cons value (cdr a))
      (cons
       (car a)
       (lp-delete-set-nat (cdr a) (- n 1) value)))))

(defun lp-delete-set (a i value)
  (lp-delete-set-nat a (nfix i) value))

(defun lp-delete-between-p (left point right)
  (or
   (and (<= left point) (< point right))
   (and (< right left) (<= left point))
   (and (< point right) (< right left))))

(defun lp-delete-next (n i)
  (let ((i1 (+ i 1)))
    (if (equal i1 n) 0 i1)))

(defun lp-delete-bucket (key n)
  (if (and (integerp n) (< 0 n))
      (mod (lp-delete-hash key) n)
    0))

(defun lp-delete-numof-loop (a position remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if
      (lp-delete-eq-p
       (lp-delete-nth position a)
       (lp-delete-dummy))
      1
      0)
     (lp-delete-numof-loop
      a
      (+ position 1)
      (- remaining 1)))))

(defun lp-delete-numof (a lower upper)
  (if (and
       (integerp lower)
       (integerp upper)
       (< lower upper))
      (lp-delete-numof-loop a lower (- upper lower))
    0))

(defun lp-delete-loc-at
    (loc updatep update-key update-value keym)
  (if (and updatep (equal keym update-key))
      update-value
    (lp-delete-loc-apply loc keym)))

(defun-sk lp-delete-no-dummy-between-p (a start finish)
  (forall (k)
    (implies
     (and
      (integerp k)
      (<= 0 k)
      (< k (len a))
      (lp-delete-between-p start k finish)
      (not (equal k start)))
     (lp-delete-neq-p
      (lp-delete-nth k a)
      (lp-delete-dummy)))))

(defun-sk lp-delete-array-view-loc-p
    (a view loc updatep update-key update-value)
  (forall (k)
    (implies
     (and
      (integerp k)
      (<= 0 k)
      (< k (len a)))
     (let ((x (lp-delete-nth k a)))
       (implies
        (lp-delete-neq-p x (lp-delete-dummy))
        (and
         (equal
          (lp-delete-view-apply
           view
           (lp-delete-keym1 x))
          t)
         (equal
          (lp-delete-loc-at
           loc
           updatep
           update-key
           update-value
           (lp-delete-keym1 x))
          k)))))))

(defun-sk lp-delete-probe-entry-p
    (a x key-index allow-hole hole cursor)
  (forall (l)
    (implies
     (and
      (integerp l)
      (<= 0 l)
      (< l (len a))
      (lp-delete-between-p
       (lp-delete-bucket x (len a))
       l
       key-index))
     (and
      (lp-delete-neq-p (lp-delete-nth l a) x)
      (or
       (lp-delete-neq-p
        (lp-delete-nth l a)
        (lp-delete-dummy))
       (and
        allow-hole
        (equal l hole)
        (lp-delete-between-p hole cursor key-index)))))))

(defun-sk lp-delete-probe-map-p
    (a view loc updatep update-key update-value
       allow-hole hole cursor)
  (forall (x)
    (implies
     (and
      (lp-delete-key-p x)
      (equal
       (lp-delete-view-apply view (lp-delete-keym1 x))
       t))
     (let ((key-index
            (lp-delete-loc-at
             loc
             updatep
             update-key
             update-value
             (lp-delete-keym1 x))))
       (and
        (<= 0 key-index)
        (< key-index (len a))
        (lp-delete-eq-p
         (lp-delete-nth key-index a)
         x)
        (lp-delete-probe-entry-p
         a
         x
         key-index
         allow-hole
         hole
         cursor))))))

(defun lp-delete-valid-p (a view loc)
  (and
   (not
    (equal
     (lp-delete-view-apply
      view
      (lp-delete-keym1 (lp-delete-dummy)))
     t))
   (lp-delete-array-view-loc-p
    a view loc nil nil 0)
   (lp-delete-probe-map-p
    a view loc nil nil 0 nil 0 0)))

(defun-sk lp-delete-list-pointwise-p (left right)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (len left)))
     (equal
      (lp-delete-nth index left)
      (lp-delete-nth index right)))))

(defun lp-delete-list-ext-p (left right)
  (and
   (equal (len left) (len right))
   (lp-delete-list-pointwise-p left right)))

(defun-sk lp-delete-set-function-equality-p
    (new old index value)
  (forall (argument)
    (implies
     (and
      (integerp argument)
      (<= 0 argument)
      (< argument (len new)))
     (equal
      (lp-delete-nth argument new)
      (if (equal argument index)
          value
        (lp-delete-nth argument old))))))

(defun lp-delete-distance (finish cursor length)
  (if (<= finish cursor)
      (+ (- length cursor) finish)
    (- finish cursor)))

(defun lp-delete-loop-state-p
    (f0 a hole cursor previous-cursor view loc)
  (and
   (<= 0
       (lp-delete-distance f0 previous-cursor (len a)))
   (<
    (lp-delete-distance f0 cursor (len a))
    (lp-delete-distance f0 previous-cursor (len a)))
   (<= 0 f0)
   (< f0 (len a))
   (<= 0 hole)
   (< hole (len a))
   (<= 0 cursor)
   (< cursor (len a))
   (not (equal hole f0))
   (lp-delete-eq-p
    (lp-delete-nth hole a)
    (lp-delete-dummy))
   (lp-delete-eq-p
    (lp-delete-nth f0 a)
    (lp-delete-dummy))
   (lp-delete-between-p hole cursor f0)
   (lp-delete-no-dummy-between-p a cursor f0)
   (not
    (equal
     (lp-delete-view-apply
      view
      (lp-delete-keym1 (lp-delete-dummy)))
     t))
   (lp-delete-array-view-loc-p
    a view loc nil nil 0)
   (lp-delete-probe-map-p
    a view loc nil nil 0 t hole cursor)))

(defun-sk lp-delete-final-loc-array-obligation-p
    (original updated view)
  (forall (loc2 a3)
    (implies
     (and
      (lp-delete-loc-function-p loc2)
      (lp-delete-key-list-p a3))
     (implies
      (equal (len a3) (len updated))
      (implies
       (and
        (equal
         (lp-delete-numof a3 0 (len a3))
         (lp-delete-numof updated 0 (len a3)))
        (lp-delete-valid-p a3 view loc2))
       (and
        (equal
         (lp-delete-numof a3 0 (len a3))
         (lp-delete-numof original 0 (len a3)))
        (lp-delete-valid-p a3 view loc2)))))))

(defun lp-delete-updated-state-p
    (f0 original updated j i i1 xi view loc)
  (and
   (<= 0 (lp-delete-distance f0 i (len original)))
   (<
    (lp-delete-distance f0 i1 (len updated))
    (lp-delete-distance f0 i (len original)))
   (<= 0 f0)
   (< f0 (len updated))
   (<= 0 i1)
   (< i1 (len updated))
   (<= 0 i1)
   (< i1 (len updated))
   (not (equal i1 f0))
   (lp-delete-eq-p
    (lp-delete-nth i1 updated)
    (lp-delete-dummy))
   (lp-delete-eq-p
    (lp-delete-nth f0 updated)
    (lp-delete-dummy))
   (lp-delete-between-p i1 i1 f0)
   (lp-delete-no-dummy-between-p updated i1 f0)
   (not
    (equal
     (lp-delete-view-apply
      view
      (lp-delete-keym1 (lp-delete-dummy)))
     t))
   (lp-delete-array-view-loc-p
    updated
    view
    loc
    t
    (lp-delete-keym1 xi)
    j)
   (lp-delete-probe-map-p
    updated
    view
    loc
    t
    (lp-delete-keym1 xi)
    j
    t
    i1
    i1)
   (lp-delete-final-loc-array-obligation-p
    original updated view)))

(defun-sk lp-delete-all-a2-p
    (f0 original set1 j i i1 xi view loc)
  (forall (a2)
    (implies
     (and
      (lp-delete-key-list-p a2)
      (lp-delete-list-ext-p a2 set1))
     (let* ((o4 (lp-delete-dummy))
            (set2 (lp-delete-set set1 i1 o4)))
       (and
        (<= 0 i1)
        (< i1 (len set1))
        (implies
         (equal (len set2) (len set1))
         (implies
          (lp-delete-set-function-equality-p
           set2 set1 i1 o4)
          (lp-delete-updated-state-p
           f0
           original
           set2
           j
           i
           i1
           xi
           view
           loc))))))))

(defun lp-delete-after-first-set-p
    (f0 a j i i1 xi view loc)
  (let ((set1 (lp-delete-set a j xi)))
    (and
     (<= 0 j)
     (< j (len a))
     (implies
      (equal (len set1) (len a))
      (implies
       (lp-delete-set-function-equality-p
        set1 a j xi)
       (lp-delete-all-a2-p
        f0 a set1 j i i1 xi view loc))))))

(defun-sk lp-delete-all-a1-p
    (f0 a j i i1 xi view loc)
  (forall (a1)
    (implies
     (and
      (lp-delete-key-list-p a1)
      (lp-delete-list-ext-p a1 a))
     (lp-delete-after-first-set-p
      f0 a j i i1 xi view loc))))

(defun-sk lp-delete-o4-exists-p (o3 i1 j r)
  (exists (o4)
    (and
     (booleanp o4)
     (if (< i1 j)
         (equal o4 (if (< j r) t nil))
       (equal o4 nil))
     (if (equal o4 t)
         (equal o3 t)
       (if (<= r i1)
           (equal o3 (if (< i1 j) t nil))
         (equal o3 nil))))))

(defun lp-delete-o3-relation-p (o2 o3 i1 j r)
  (if (equal o2 t)
      (equal o3 t)
    (lp-delete-o4-exists-p o3 i1 j r)))

(defun-sk lp-delete-all-o3-p
    (f0 a j i i1 xi view loc r o2)
  (forall (o3)
    (implies
     (booleanp o3)
     (implies
      (lp-delete-o3-relation-p o2 o3 i1 j r)
      (if (equal o3 t)
          (lp-delete-loop-state-p
           f0 a j i1 i view loc)
        (lp-delete-all-a1-p
         f0 a j i i1 xi view loc))))))

(defun-sk lp-delete-all-o2-p
    (f0 a j i i1 xi view loc r)
  (forall (o2)
    (implies
     (booleanp o2)
     (implies
      (if (< j r)
          (equal o2 (if (<= r i1) t nil))
        (equal o2 nil))
      (lp-delete-all-o3-p
       f0 a j i i1 xi view loc r o2)))))

(defun lp-delete-nonempty-next-branch-p
    (f0 a j i i1 xi view loc)
  (let ((n (len a))
        (r (lp-delete-bucket xi (len a))))
    (and
     (< 0 n)
     (implies
      (and (<= 0 r) (< r n))
      (lp-delete-all-o2-p
       f0 a j i i1 xi view loc r)))))

(defun-sk lp-delete-fact13-p (a j i view loc)
  (forall (x)
    (implies
     (and
      (lp-delete-key-p x)
      (equal
       (lp-delete-view-apply view (lp-delete-keym1 x))
       t))
     (let ((k (lp-delete-loc-apply loc (lp-delete-keym1 x))))
       (and
        (<= 0 k)
        (< k (len a))
        (lp-delete-eq-p (lp-delete-nth k a) x)
        (lp-delete-probe-entry-p
         a x k t j i))))))

(defun lp-delete-hypotheses-p (f0 a j i view loc)
  (and
   (integerp f0)
   (integerp j)
   (integerp i)
   (lp-delete-key-list-p a)
   (lp-delete-view-function-p view)
   (lp-delete-loc-function-p loc)
   (<= 0 f0)
   (< f0 (len a))
   (<= 0 j)
   (< j (len a))
   (<= 0 i)
   (< i (len a))
   (not (equal j f0))
   (lp-delete-eq-p
    (lp-delete-nth j a)
    (lp-delete-dummy))
   (lp-delete-eq-p
    (lp-delete-nth f0 a)
    (lp-delete-dummy))
   (lp-delete-between-p j i f0)
   (lp-delete-no-dummy-between-p a i f0)
   (not
    (equal
     (lp-delete-view-apply
      view
      (lp-delete-keym1 (lp-delete-dummy)))
     t))
   (lp-delete-array-view-loc-p
    a view loc nil nil 0)
   (lp-delete-fact13-p a j i view loc)))

(defun lp-delete-conclusion-p (f0 a j i view loc)
  (let* ((n (len a))
         (i1 (lp-delete-next n i))
         (xi (lp-delete-nth i1 a))
         (o1 (lp-delete-dummy)))
    (and
     (<= 0 i1)
     (< i1 (len a))
     (implies
      (iff
       (lp-delete-neq-p xi o1)
       (not
        (equal
         (lp-delete-keym1 xi)
         (lp-delete-keym1 o1))))
      (if (lp-delete-neq-p xi o1)
          (lp-delete-nonempty-next-branch-p
           f0 a j i i1 xi view loc)
        (lp-delete-valid-p a view loc))))))

(defun ntp4vc-linear-probing-delete-vc-statement
    (f0 a j i view1 loc1)
  (implies
   (and
    (lp-delete-context-p)
    (lp-delete-hypotheses-p
     f0 a j i view1 loc1))
   (lp-delete-conclusion-p
    f0 a j i view1 loc1)))

(value-triple :itpeval-statement-checked)
:q
