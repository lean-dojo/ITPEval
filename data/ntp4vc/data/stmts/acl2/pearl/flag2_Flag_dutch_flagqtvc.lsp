;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/flag2_Flag_dutch_flagqtvc: the Dutch-flag loop verification
;; condition, including monochromatic regions, color-occurrence preservation,
;; swap branches, and the final three-color partition. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These three ACL2 objects are an exact representation of the source color
;; datatype.  The source's globally chosen Inhabited value is represented by
;; a conservative nullary interface and constrained explicitly in the final
;; statement predicate.

(defun ntp4vc-df-color-p (value)
  (or
   (equal value :blue)
   (equal value :white)
   (equal value :red)))

(defstub ntp4vc-df-default-color () t)

(defun ntp4vc-df-color-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (ntp4vc-df-color-p (car xs))
     (ntp4vc-df-color-list-p (cdr xs)))))

;; Int.toNat maps negative integers to zero.  List getElem! then returns the
;; chosen default color when the resulting natural index is out of bounds.

(defun ntp4vc-df-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun ntp4vc-df-nth-color (xs index)
  (let ((tail
         (nthcdr
          (ntp4vc-df-int-to-nat index)
          xs)))
    (if (consp tail)
        (car tail)
      (ntp4vc-df-default-color))))

;; Every integer index in the half-open interval [lower, upper) has the
;; specified color.

(defun-sk ntp4vc-df-monochrome-p
    (xs lower upper color)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (ntp4vc-df-nth-color xs index)
       color)))))

;; This terminating recursion is the source nb_occ equation specialized to
;; the total indexing function of a color list.

(defun ntp4vc-df-nb-occ
    (xs lower upper color)
  (declare
   (xargs
    :measure
    (nfix
     (- (ifix upper)
        (ifix lower)))))
  (if (and
       (integerp lower)
       (integerp upper)
       (< lower upper))
      (+
       (if (equal
            (ntp4vc-df-nth-color xs (- upper 1))
            color)
           1
         0)
       (ntp4vc-df-nb-occ
        xs lower (- upper 1) color))
    0))

;; Universal equality of occurrence counts over the three source colors.

(defun ntp4vc-df-same-occurrences-p
    (left right upper)
  (and
   (equal
    (ntp4vc-df-nb-occ left 0 upper :blue)
    (ntp4vc-df-nb-occ right 0 upper :blue))
   (equal
    (ntp4vc-df-nb-occ left 0 upper :white)
    (ntp4vc-df-nb-occ right 0 upper :white))
   (equal
    (ntp4vc-df-nb-occ left 0 upper :red)
    (ntp4vc-df-nb-occ right 0 upper :red))))

;; The two universal components of the source swap specification.

(defun-sk ntp4vc-df-other-positions-unchanged-p
    (new old first second)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (not (equal index first))
       (not (equal index second)))
      (equal
       (ntp4vc-df-nth-color new index)
       (ntp4vc-df-nth-color old index))))))

(defun-sk ntp4vc-df-interval-occurrences-preserved-p
    (new old first second)
  (forall (lower upper color)
    (implies
     (and
      (integerp lower)
      (integerp upper)
      (ntp4vc-df-color-p color))
     (implies
      (and
       (<= lower first)
       (< first upper)
       (<= lower second)
       (< second upper))
      (equal
       (ntp4vc-df-nb-occ new lower upper color)
       (ntp4vc-df-nb-occ old lower upper color))))))

(defun ntp4vc-df-swap-premise-p
    (new old first second)
  (and
   (equal
    (ntp4vc-df-nth-color new first)
    (ntp4vc-df-nth-color old second))
   (equal
    (ntp4vc-df-nth-color new second)
    (ntp4vc-df-nth-color old first))
   (ntp4vc-df-other-positions-unchanged-p
    new old first second)
   (ntp4vc-df-interval-occurrences-preserved-p
    new old first second)))

;; The invariant assumed for an arbitrary loop state.

(defun ntp4vc-df-loop-invariant-p
    (original current b i r)
  (and
   (<= 0 b)
   (<= b i)
   (<= i r)
   (<= r (len current))
   (ntp4vc-df-monochrome-p current 0 b :blue)
   (ntp4vc-df-monochrome-p current b i :white)
   (ntp4vc-df-monochrome-p
    current r (len current) :red)
   (ntp4vc-df-same-occurrences-p
    current original (len current))))

;; Consequences of the Blue branch, universally quantified over every list
;; satisfying the source swap specification.

(defun ntp4vc-df-blue-conclusion-p
    (original new b i r)
  (and
   (<= 0 (- r i))
   (< (- r (+ i 1)) (- r i))
   (<= 0 (+ b 1))
   (<= (+ b 1) (+ i 1))
   (<= (+ i 1) r)
   (<= r (len new))
   (ntp4vc-df-monochrome-p
    new 0 (+ b 1) :blue)
   (ntp4vc-df-monochrome-p
    new (+ b 1) (+ i 1) :white)
   (ntp4vc-df-monochrome-p
    new r (len new) :red)
   (ntp4vc-df-same-occurrences-p
    new original (len new))))

(defun-sk ntp4vc-df-blue-continuation-p
    (original current b i r)
  (forall (new)
    (implies
     (ntp4vc-df-color-list-p new)
     (implies
      (equal (len new) (len current))
      (implies
       (ntp4vc-df-swap-premise-p
        new current b i)
       (ntp4vc-df-blue-conclusion-p
        original new b i r))))))

;; The White branch changes only the middle boundary.

(defun ntp4vc-df-white-conclusion-p
    (original current b i r)
  (and
   (<= 0 (- r i))
   (< (- r (+ i 1)) (- r i))
   (<= 0 b)
   (<= b (+ i 1))
   (<= (+ i 1) r)
   (<= r (len current))
   (ntp4vc-df-monochrome-p current 0 b :blue)
   (ntp4vc-df-monochrome-p
    current b (+ i 1) :white)
   (ntp4vc-df-monochrome-p
    current r (len current) :red)
   (ntp4vc-df-same-occurrences-p
    current original (len current))))

;; Consequences of the Red branch, again retaining the internal universal
;; quantifier over every list satisfying the source swap specification.

(defun ntp4vc-df-red-conclusion-p
    (original new b i r)
  (and
   (<= 0 (- r i))
   (< (- (- r 1) i) (- r i))
   (<= 0 b)
   (<= b i)
   (<= i (- r 1))
   (<= (- r 1) (len new))
   (ntp4vc-df-monochrome-p new 0 b :blue)
   (ntp4vc-df-monochrome-p new b i :white)
   (ntp4vc-df-monochrome-p
    new (- r 1) (len new) :red)
   (ntp4vc-df-same-occurrences-p
    new original (len new))))

(defun-sk ntp4vc-df-red-continuation-p
    (original current b i r)
  (forall (new)
    (implies
     (ntp4vc-df-color-list-p new)
     (implies
      (equal (len new) (len current))
      (implies
       (ntp4vc-df-swap-premise-p
        new current (- r 1) i)
       (ntp4vc-df-red-conclusion-p
        original new b i r))))))

;; When i is no longer below r, the partition boundaries remain existential
;; witnesses inside the conclusion, exactly as in the source statement.

(defun-sk ntp4vc-df-final-partition-p
    (current)
  (exists (blue-end red-start)
    (and
     (integerp blue-end)
     (integerp red-start)
     (ntp4vc-df-monochrome-p
      current 0 blue-end :blue)
     (ntp4vc-df-monochrome-p
      current blue-end red-start :white)
     (ntp4vc-df-monochrome-p
      current red-start (len current) :red))))

(defun ntp4vc-df-termination-conclusion-p
    (original current)
  (and
   (ntp4vc-df-final-partition-p current)
   (ntp4vc-df-same-occurrences-p
    current original (len current))))

;; The source match on current[i] is represented by the exact three cases of
;; the color datatype.

(defun ntp4vc-df-loop-step-p
    (original current b i r)
  (if (< i r)
      (and
       (<= 0 i)
       (< i (len current))
       (let ((color
              (ntp4vc-df-nth-color current i)))
         (if (equal color :blue)
             (and
              (<= 0 b)
              (< b (len current))
              (<= 0 i)
              (< i (len current))
              (ntp4vc-df-blue-continuation-p
               original current b i r))
           (if (equal color :white)
               (ntp4vc-df-white-conclusion-p
                original current b i r)
             (if (equal color :red)
                 (and
                  (<= 0 (- r 1))
                  (< (- r 1) (len current))
                  (<= 0 i)
                  (< i (len current))
                  (ntp4vc-df-red-continuation-p
                   original current b i r))
               nil)))))
    (ntp4vc-df-termination-conclusion-p
     original current)))

;; Preserve the source's nested universal continuation over every typed loop
;; state with the same list length as the original input.

(defun-sk ntp4vc-df-loop-vc-p
    (original)
  (forall (r i b current)
    (implies
     (and
      (integerp r)
      (integerp i)
      (integerp b)
      (ntp4vc-df-color-list-p current))
     (implies
      (equal (len current) (len original))
      (implies
       (ntp4vc-df-loop-invariant-p
        original current b i r)
       (ntp4vc-df-loop-step-p
        original current b i r))))))

(defun ntp4vc-df-initial-state-p (original)
  (let ((length (len original)))
    (and
     (<= 0 0)
     (<= 0 0)
     (<= 0 length)
     (<= length (len original))
     (ntp4vc-df-monochrome-p original 0 0 :blue)
     (ntp4vc-df-monochrome-p original 0 0 :white)
     (ntp4vc-df-monochrome-p
      original length (len original) :red))))

(defun
    ntp4vc-pearl-flag2-flag-dutch-flagqtvc-statement
    (original)
  (implies
   (and
    (ntp4vc-df-color-list-p original)
    (ntp4vc-df-color-p
     (ntp4vc-df-default-color)))
   (and
    (ntp4vc-df-initial-state-p original)
    (ntp4vc-df-loop-vc-p original))))

(value-triple :itpeval-statement-checked)
:q
