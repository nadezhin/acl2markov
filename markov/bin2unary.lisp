(in-package "ACL2")
(include-book "markov")
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(defund word-01-p (x)
  (declare (xargs :guard t))
  (wordp x '(#\0 #\1)))

(defrule |word-01-p is true-listp|
  (implies (word-01-p x) (true-listp x))
  :enable word-01-p)

(defruled |nth word-01-p is member|
  (implies
    (and (word-01-p inp)
         (natp i)
         (< i (len inp)))
    (member (nth i inp) '(#\0 #\1)))
  :enable word-01-p)

(defrule |take word-01-p|
  (implies (and (word-01-p x)
                (<= n (len x)))
           (word-01-p (take n x)))
  :enable word-01-p)

(defrule |nthcdr word-01-p|
  (implies (word-01-p x)
           (word-01-p (nthcdr n x)))
  :enable word-01-p)

(defrule listpos-append-word-01-p
  (implies
    (and
      (word-01-p x)
      (consp pat)
      (not (member (car pat) '(#\0 #\1))))
    (equal (listpos pat (append x y))
           (and (listpos pat y)
                (+ (len x) (listpos pat y)))))
  :enable word-01-p)

(defrule sublistp-append-word-01-p
  (implies
    (and
      (word-01-p x)
      (not (member (car pat) '(#\0 #\1))))
    (equal (sublistp pat (append x y))
           (sublistp pat y)))
  :enable word-01-p)

(defund word-0bar-p (x)
  (declare (xargs :guard t))
  (wordp x '(#\0 #\|)))

(defrule |word-0bar-p is true-listp|
  (implies (word-0bar-p x) (true-listp x))
  :enable word-0bar-p)

(defruled |nth word-0bar-p is member|
  (implies
    (and (word-0bar-p inp)
         (natp i)
         (< i (len inp)))
    (member (nth i inp) '(#\0 #\|)))
  :enable word-0bar-p)

(defrule |take word-0bar-p|
  (implies (and (word-0bar-p x)
                (<= n (len x)))
           (word-0bar-p (take n x)))
  :enable word-0bar-p)

(defrule |nthcdr word-0bar-p|
  (implies (word-0bar-p x)
           (word-0bar-p (nthcdr n x)))
  :enable word-0bar-p)

(defrule listpos-append-word-0bar-p
  (implies
    (and
      (word-0bar-p x)
      (consp pat)
      (not (member (car pat) '(#\0 #\|))))
    (equal (listpos pat (append x y))
           (and (listpos pat y)
                (+ (len x) (listpos pat y)))))
  :enable word-0bar-p)

(defrule sublistp-append-word-0bar-p
  (implies
    (and
      (word-0bar-p x)
      (not (member (car pat) '(#\0 #\|))))
    (equal (sublistp pat (append x y))
           (sublistp pat y)))
  :enable word-0bar-p)

;------------------------------------

(defconst *scheme-bin2unary-en*
  (list
    (mks->  "|0" "0||")
    (mks->  "1"  "0|" )
    (mks->  "0"  ""   )))

(defconst *scheme-bin2unary-ru*
  (list
    (mks->  "1"  "0|" )
    (mks->  "|0" "0||")
    (mks->  "0"  ""   )))

(defund replace-ones (x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
        ((eql (car x) #\1) (list* #\0 #\| (replace-ones (cdr x))))
        (t (list* (car x) (replace-ones (cdr x))))))

(defruled |word-0bar-p replace-ones|
  (implies (word-01-p x)
           (word-0bar-p (replace-ones x)))
  :enable (replace-ones word-0bar-p word-01-p)
  :induct (len x))

(defrule |replace-ones append|
  (equal (replace-ones (append x y))
         (append (replace-ones x) (replace-ones y)))
  :enable replace-ones
  :induct (len x))

(defund step1 (inp n)
  (declare (xargs :guard (and (word-01-p inp) (natp n))))
  (append (replace-ones (take n inp)) (nthcdr n inp)))

(defrule |step1 0|
  (equal (step1 inp 0) inp)
  :enable step1)

(defrule |step1 len|
  (implies
    (word-01-p inp)
    (equal (step1 inp (len inp))
           (replace-ones inp)))
  :enable step1)

(defrule |step1 same when #\0|
  (implies
    (and
      (word-01-p inp)
      (natp n)
      (< n (len inp))
      (eql (nth n inp) #\0))
    (equal (step1 inp (1+ n))
           (step1 inp n)))
  :enable (step1 |take n+1| |nthcdr as cons|))

(defruled |step1 applicable when #\1|
  (implies
    (and
      (word-01-p inp)
      (natp n)
      (< n (len inp))
      (eql (nth n inp) #\1))
   (equal
      (applicable *scheme-bin2unary-ru* (step1 inp n))
      (mks-> "1" "0|")))
  :enable (applicable step1 |word-0bar-p replace-ones|)
  :use (:instance sublistp-append-wordp
         (pat '(#\1))
         (x (replace-ones (take n inp)))
         (alphabet '(#\0 #\|))
         (y (nthcdr n inp))))

(defruled |step1 substp when #\1|
  (implies
    (and
      (word-01-p inp)
      (natp n)
      (< n (len inp))
      (eql (nth n inp) #\1))
    (substp (step1 inp n) '(#\1) '(#\0 #\|) (step1 inp (1+ n))))
  :prep-lemmas (
    (defrule lemma
      (implies
        (word-0bar-p x)
        (left-wingp x '(#\1)))
      :enable (word-0bar-p |left-wingp as left-wingp1| left-wingp1)
      :induct (len x)))
  :enable (step1 |word-0bar-p replace-ones|
           |take n+1| |nthcdr as cons|)
  :use (:instance substp-lemma
         (x (step1 inp n))
         (l '(#\1))
         (r '(#\0 #\|))
         (y (step1 inp (1+ n)))
         (lw (replace-ones (take n inp)))
         (rw (nthcdr (1+ n) inp))))

(defruled |step1 correct when #\1|
  (implies
    (and
      (word-01-p inp)
      (natp n)
      (< n (len inp))
      (eql (nth n inp) #\1))
    (simple-stepp
      *scheme-bin2unary-ru*
      (step1 inp n)
      (step1 inp (1+ n))))
  :enable (simple-stepp |step1 applicable when #\1| |step1 substp when #\1|))

(defruled |step1 correct a|
  (implies
    (and
      (word-01-p inp)
      (natp n)
      (< n (len inp)))
    (simple-steps
      *scheme-bin2unary-ru*
      (if (eql (nth n inp) #\1) 1 0)
      (step1 inp n)
      (step1 inp (1+ n))))
  :enable |step1 correct when #\1|
  :use (:instance |nth word-01-p is member|
         (i n)))

(defruled |step1 correct all|
  (implies
    (and
      (word-01-p inp)
      (natp n)
      (<= n (len inp)))
    (simple-steps
      *scheme-bin2unary-ru*
      (duplicity #\1 (take n inp))
      inp
      (step1 inp n)))
  :disable duplicity-of-append
  :induct (dec-induct n)
  :hints (("subgoal *1/2" :do-not-induct t
                          :use ((:instance simple-steps-cat
                                  (scheme *scheme-bin2unary-ru*)
                                  (m (duplicity #\1 (take (1- n) inp)))
                                  (n (duplicity #\1 (list (nth (1- n) inp))))
                                  (x inp)
                                  (y (step1 inp (1- n)))
                                  (z (step1 inp n)))
                                (:instance |step1 correct a|
                                  (n (1- n)))
                                (:instance duplicity-of-append
                                  (a #\1)
                                  (x (take (1- n) inp))
                                  (y (list (nth (1- n) inp))))
                                (:instance |take n+1|
                                  (x inp)
                                  (n (1- n)))))))

(defund digit-count (x)
  (declare (xargs :guard t))
  (cond ((atom x) 0)
        ((or (eql (car x) #\0) (eql (car x) #\1)) (1+ (digit-count (cdr x))))
        (t (digit-count (cdr x)))))

(defrule |digit-count append|
  (equal (digit-count (append x y))
         (+ (digit-count x) (digit-count y)))
  :enable digit-count)

(defund val (x)
  (declare (xargs :guard t))
  (cond ((atom x) 0)
        ((or (eql (car x) #\1) (eql (car x) #\|))
         (+ (expt 2 (digit-count (cdr x)))
            (val (cdr x))))
        (t (val (cdr x)))))

(defrule |val append|
  (equal (val (append x y))
         (+ (val y) (* (val x) (expt 2 (digit-count y)))))
  :prep-books ((include-book "arithmetic/top" :dir :system))
  :enable (val digit-count append))

(defrule |duplicity bar <= val|
  (<= (duplicity #\| x)
      (val x))
  :prep-books ((include-book "arithmetic/top" :dir :system))
  :enable (duplicity val)
  :rule-classes :linear)

(defrule |duplicity 1 <= val|
  (<= (duplicity #\1 x)
      (val x))
  :prep-books ((include-book "arithmetic/top" :dir :system))
  :enable (duplicity val)
  :rule-classes :linear)

(defund step2 (inp n)
  (declare (xargs :guard (and (word-01-p inp) (natp n))))
  (append (repeat n #\0)
          (repeat (val (take n inp)) #\|)
          (replace-ones (nthcdr n inp))))

(defrule |word-01-p repeat #\0|
  (word-01-p (repeat n #\0))
  :enable (word-01-p wordp repeat)
  :induct (dec-induct n))

(defrule |word-0bar-p repeat #\0|
  (word-0bar-p (repeat n #\0))
  :enable (word-0bar-p wordp repeat)
  :induct (dec-induct n))

(defrule |word-0bar-p repeat bar|
  (word-0bar-p (repeat n #\|))
  :enable (word-0bar-p wordp repeat)
  :induct (dec-induct n))

(defruled |step2 applicable|
  (implies
    (and
      (natp n)
      (posp i)
      (word-0bar-p y))
    (equal
      (applicable
        *scheme-bin2unary-ru*
        (append (repeat n #\0) (repeat i #\|) (cons #\0 y)))
      (mks-> "|0" "0||")))
  :prep-lemmas (
    (defrule lemma1
      (implies
        (and (natp n)
             (posp i)
             (word-0bar-p y))
        (not (sublistp '(#\1)
                       (append (repeat n #\0)
                               (repeat i #\|)
                               (cons #\0 y)))))
      :cases ((sublistp '(#\1) y))
      :hints (("subgoal 1" :use (:instance sublistp-append-word-0bar-p
                                  (pat '(#\1))
                                  (x y)
                                  (y nil)))))
    (defrule lemma2
      (implies
         (posp i)
         (sublistp
           '(#\| #\0)
           (append (repeat i #\|) (cons #\0 y))))
      :enable (sublistp repeat)
      :induct (dec-induct i)))
  :enable applicable)

(defruled |step2 substp|
  (implies
    (and
      (natp n)
      (posp i)
      (natp j))
    (substp
      (append (repeat n #\0) (repeat i #\|) (list #\0) (repeat j #\|) y)
      '(#\| #\0)
      '(#\0 #\| #\|)
      (append (repeat n #\0) (repeat (1- i) #\|) (list #\0) (repeat (+ 2 j) #\|) y)))
  :prep-lemmas (
    (defrule lemma1
      (implies (natp k)
               (left-wingp1 (repeat k #\|) '(#\| #\0)))
      :enable (|left-wingp as left-wingp1| left-wingp1)
      :induct (dec-induct k)
      :hints (("subgoal *1/2" :expand (repeat k #\|))))
    (defrule lemma2
      (implies
        (and
          (natp n)
          (natp k))
        (left-wingp (append (repeat n #\0) (repeat k #\|)) '(#\| #\0)))
      :enable (|left-wingp as left-wingp1| left-wingp1)
      :induct (dec-induct n)
      :hints (("subgoal *1/2" :expand (repeat n #\0))))
    (defrule lemma3
      (implies
        (natp n)
        (equal (cons a (repeat n a))
               (repeat (1+ n) a)))
     :enable repeat
     :induct (dec-induct n))
   (defrule lemma4
     (implies
       (equal (len x) n)
       (equal (nthcdr n (append x y)) y))
     :induct (cdr-dec-induct x n)))
  :use (:instance substp-lemma
         (x (append (repeat n #\0) (repeat i #\|) (list #\0) (repeat j #\|) y))
         (l '(#\| #\0))
         (r '(#\0 #\| #\|))
         (y (append (repeat n #\0) (repeat (1- i) #\|) (list #\0) (repeat (+ 2 j) #\|) y))
         (lw (append (repeat n #\0) (repeat (1- i) #\|)))
         (rw (append (repeat j #\|) y))))

(defruled |step2 correct low|
  (implies
    (and
      (natp n)
      (posp i)
      (natp j)
      (word-0bar-p y))
    (simple-stepp
      *scheme-bin2unary-ru*
      (append (repeat n #\0) (repeat i #\|) (list #\0) (repeat j #\|) y)
      (append (repeat n #\0) (repeat (1- i) #\|) (list #\0) (repeat (+ 2 j) #\|) y)))
  :prep-lemmas (
    (defrule lemma1
      (implies
        (word-0bar-p y)
        (word-0bar-p (append (repeat j #\|) y)))
      :enable (word-0bar-p repeat)))
  :enable (simple-stepp |step2 applicable|)
  :use |step2 substp|)

(defruled |step2 correct a|
  (implies
    (and
      (natp n)
      (natp i)
      (natp j)
      (word-0bar-p y))
    (simple-steps
      *scheme-bin2unary-ru*
      i
      (append (repeat n #\0) (repeat i #\|) (list #\0) (repeat j #\|) y)
      (append (repeat n #\0) (list #\0) (repeat (+ (* 2 i) j) #\|) y)))
  :prep-lemmas (
    (defrule lemma1
      (implies
        (and
          (natp n)
          (posp i)
          (natp j)
          (word-0bar-p y))
        (simple-steps
          *scheme-bin2unary-ru*
          1
          (append (repeat n #\0) (repeat i #\|) (list #\0) (repeat j #\|) y)
          (append (repeat n #\0) (repeat (1- i) #\|) (list #\0) (repeat (+ 2 j) #\|) y)))
      :disable simple-steps-1
      :use ((:instance simple-steps-1
              (scheme *scheme-bin2unary-ru*)
              (x (append (repeat n #\0) (repeat i #\|) (list #\0) (repeat j #\|) y))
              (y (append (repeat n #\0) (repeat (1- i) #\|) (list #\0) (repeat (+ 2 j) #\|) y)))
            (:instance |step2 correct low|)))
    (defrule lemma
      (implies
        (and
          (natp n)
          (natp i)
          (natp s)
          (<= (* 2 i) s)
          (word-0bar-p y))
        (simple-steps
          *scheme-bin2unary-ru*
          i
          (append (repeat n #\0) (repeat i #\|) (list #\0) (repeat (- s (* 2 i)) #\|) y)
          (append (repeat n #\0) (list #\0) (repeat s #\|) y)))
    :induct (dec-induct i)
    :hints (
      ("subgoal *1/2" :use ((:instance lemma1
                              (j (- s (* 2 i))))
                            (:instance simple-steps-cat
                              (scheme *scheme-bin2unary-ru*)
                              (m 1)
                              (n (1- i))
                              (x (append (repeat n #\0) (repeat i #\|) (list #\0) (repeat (- s (* 2 i)) #\|) y))
                              (y (append (repeat n #\0) (repeat (1- i) #\|) (list #\0) (repeat (- s (* 2 (1- i))) #\|) y))
                              (z (append (repeat n #\0) (list #\0) (repeat s  #\|) y))))))))
  :use (:instance lemma
         (s (+ (* 2 i) j))))

(defrule |val take n+1 inp|
  (implies
    (and
      (word-01-p inp)
      (natp n)
      (< n (len inp)))
    (equal (val (take (+ 1 n) inp))
           (+ (* 2 (val (take n inp)))
              (if (eql (nth n inp) #\1) 1 0))))
  :enable (|take n+1| digit-count)
  :use ((:instance |val append|
          (x (take n inp))
          (y (list (nth n inp))))
        (:instance |nth word-01-p is member|
          (i n))))

(defruled |step2 correct q|
  (implies
    (and
      (word-01-p inp)
      (natp n)
      (< n (len inp)))
    (simple-steps
      *scheme-bin2unary-ru*
      (val (take n inp))
      (step2 inp n)
      (step2 inp (1+ n))))
  :prep-lemmas (
    (defrule lemma1
      (implies
        (natp n)
        (equal
          (repeat (+ 1 n) a)
          (cons a (repeat n a))))
      :enable repeat)
     (defrule lemma2
       (implies
         (and
           (word-01-p inp)
           (natp n)
           (< n (len inp))
           (not (equal (nth n inp) #\1)))
         (equal (cons #\0 (replace-ones (nthcdr (+ 1 n) inp)))
                (replace-ones (nthcdr n inp))))
      :enable (|nthcdr as cons| replace-ones)
      :use (:instance |nth word-01-p is member|
             (i n)))
     (defrule lemma3
       (implies
         (and
           (word-01-p inp)
           (natp n)
           (< n (len inp))
           (equal (nth n inp) #\1))
         (equal (list* #\0 #\| (replace-ones (nthcdr (+ 1 n) inp)))
                (replace-ones (nthcdr n inp))))
      :enable (|nthcdr as cons| replace-ones)
      :use (:instance |nth word-01-p is member|
             (i n))))
  :enable (step2)
  :use (:instance |step2 correct a|
         (i (val (take n inp)))
         (j (if (eql (nth n inp) #\1) 1 0))
         (y (replace-ones (nthcdr (1+ n) inp)))))

(defruled |step2 correct 4|
  (implies
    (and
      (word-01-p inp)
      (natp n)
      (<= n (len inp)))
    (simple-steps
      *scheme-bin2unary-ru*
      (- (val (take n inp))
         (duplicity #\1 (take n inp)))
      (step2 inp 0)
      (step2 inp n)))
  :prep-lemmas (
    (defrule lemma
      (implies
        (and
          (word-01-p inp)
          (posp n)
          (<= n (len inp)))
        (equal
          (+ (val (take (+ -1 n) inp))
             (val (take (+ -1 n) inp))
             (- (duplicity #\1 (take (+ -1 n) inp))))
          (+ (val (take n inp))
             (- (duplicity #\1 (take n inp))))))
      :use ((:instance duplicity-of-append
              (a #\1)
              (x (take (+ -1 n) inp))
              (y (list (nth n inp))))
            (:instance |val take n+1 inp|
              (n (1- n)))
            (:instance |take n+1|
              (x inp)
             (n (1- n))))))
  :induct (dec-induct n)
  :hints (
    ("subgoal *1/2" :use ((:instance |step2 correct q|
                            (n (1- n)))
                          (:instance simple-steps-cat
                              (scheme *scheme-bin2unary-ru*)
                              (m (- (val (take (1- n) inp))
                                    (duplicity #\1 (take (1- n) inp))))
                              (n (val (take (1- n) inp)))
                              (x (step2 inp 0))
                              (y (step2 inp (1- n)))
                              (z (step2 inp n)))))))

#|
(step2 '(#\1 #\0 #\1) 0)
(step2 '(#\1 #\0 #\1) 1)
(step2 '(#\1 #\0 #\1) 2)
(step2 '(#\1 #\0 #\1) 3)
|#
(defruled |step2 0|
  (implies
    (word-01-p inp)
    (equal (step2 inp 0)
           (step1 inp (len inp))))
  :enable step2)

(defruled |step2 len|
  (implies
    (word-01-p inp)
    (equal (step2 inp (len inp))
           (append (repeat (len inp) #\0)
                   (repeat (val inp) #\|))))
  :enable step2)

(defruled |step1 and step2 correct|
  (implies
    (word-01-p inp)
    (simple-steps
      *scheme-bin2unary-ru*
      (val inp)
      inp
      (append (repeat (len inp) #\0)
              (repeat (val inp) #\|))))
  :enable (|step2 0| |step2 len|)
  :use ((:instance simple-steps-cat
         (scheme *scheme-bin2unary-ru*)
         (m (duplicity #\1 inp))
         (n (- (val inp) (duplicity #\1 inp)))
         (x inp)
         (y (step2 inp 0))
         (z (append (repeat (len inp) #\0)
                    (repeat (val inp) #\|))))
        (:instance |step1 correct all|
          (n (len inp)))
        (:instance |step2 correct 4|
          (n (len inp)))))

(defund step3 (inp n)
  (declare (xargs :guard (and (integerp n) (<= n (len inp)))))
  (append (repeat (- (len inp) n) #\0)
          (repeat (val inp) #\|)))

(defruled |step3 applicable|
  (implies
    (and
      (word-01-p inp)
      (natp n)
      (< n (len inp)))
   (equal
      (applicable *scheme-bin2unary-ru* (step3 inp n))
      (mks-> "0" "")))
  :prep-lemmas (
    (defrule lemma1
      (not (sublistp '(#\1) (repeat n #\|)))
      :enable (sublistp repeat)
      :induct (dec-induct n))
    (defrule lemma2
      (not (equal #\0 (car (repeat n #\|))))
      :enable repeat)
    (defrule lemma3
      (implies
        (natp n)
        (not (sublistp '(#\| #\0) (repeat n #\|))))
      :enable (sublistp repeat prefixp)
      :induct (dec-induct n))
    (defrule lemma4
      (implies
        (posp n)
        (sublistp '(#\0) (append (repeat n #\0) x)))
      :expand (repeat n #\0)))
  :enable (applicable step3))

(defruled |step3 substp|
  (implies
    (and
      (word-01-p inp)
      (natp n)
      (< n (len inp)))
    (substp
      (step3 inp n)
      '(#\0)
      '()
      (step3 inp (1+ n))))
  :prep-lemmas (
    (defrule lemma
      (implies (equal n (len x))
               (equal (nthcdr n (append x y)) y))))
  :enable (step3 repeat)
  :use (:instance substp-lemma
         (x (step3 inp n))
         (l '(#\0))
         (r '())
         (y (step3 inp (1+ n)))
         (lw '())
         (rw (step3 inp (1+ n)))))

(defruled |step3 correct a|
  (implies
    (and
      (word-01-p inp)
      (natp n)
      (< n (len inp)))
    (simple-stepp
      *scheme-bin2unary-ru*
      (step3 inp n)
      (step3 inp (1+ n))))
  :enable (simple-stepp |step3 applicable| |step3 substp|))

(defruled |step3 correct b|
  (implies
    (and
      (word-01-p inp)
      (natp n)
      (<= n (len inp)))
    (simple-steps
      *scheme-bin2unary-ru*
      n
      (step3 inp 0)
      (step3 inp n)))
  :induct (dec-induct n)
  :hints (("subgoal *1/2" :use ((:instance simple-steps-cat
                                  (scheme *scheme-bin2unary-ru*)
                                  (m (1- n))
                                  (n 1)
                                  (x (step3 inp 0))
                                  (y (step3 inp (1- n)))
                                  (z (step3 inp n)))
                                (:instance |step3 correct a|
                                  (n (1- n)))))))

(defruled |step3 0|
  (implies
    (word-01-p inp)
    (equal (step3 inp 0)
           (step2 inp (len inp))))
  :enable (step3 |step2 len|))

(defruled |step3 len|
  (implies
    (word-01-p inp)
    (equal (step3 inp (len inp))
           (repeat (val inp) #\|)))
  :enable step3)

(defruled |step123 correct|
  (implies
    (word-01-p inp)
    (simple-steps
      *scheme-bin2unary-ru*
      (+ (val inp) (len inp))
      inp
      (repeat (val inp) #\|)))
  :enable (|step2 len| |step3 0| |step3 len|)
  :use ((:instance simple-steps-cat
          (scheme *scheme-bin2unary-ru*)
          (m (val inp))
          (n (len inp))
          (x inp)
          (y (step3 inp 0))
          (z (step3 inp (len inp))))
        |step1 and step2 correct|
        (:instance |step3 correct b|
          (n (len inp)))))

(defruled |applicable final|
  (not (applicable *scheme-bin2unary-ru* (repeat n #\|)))
  :enable (applicable repeat)
  :induct (dec-induct n))
