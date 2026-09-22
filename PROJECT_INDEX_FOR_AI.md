# 색칠 문제의 독립 저장소 인덱스

## 목적과 완료 상태

가로 n+1열, 세로 l행의 정사각 격자점을 n색으로 칠할 때 모든 방향의 단색 직사각형을 강제하는 최소 높이를 구한다. n>0에서 답은 n²(n+1)/2+1이다. 수학 증명과 Lean 일반 정리까지 완료했다.

## 먼저 읽을 파일

1. `README.md`: 한국어 문제 설명, 파일 안내, 실행 명령.
2. `solution.pdf` 또는 `solution.tex`: 완전한 한국어 풀이. PDF는 7쪽이며 실제 렌더링을 검수했다.
3. `lean/RectangleColoring/Main.lean`, `Basic.lean`: 최종 정리와 문제의 정의.
4. `lean/RectangleColoring/LowerBound.lean`: 하한의 전역 연결.
5. `solution.md`, `verify.py`: 다른 문서 형식과 독립적인 유한 검산.

`.lake/`와 `temp/`는 생성·중간 자료이므로 재탐색할 필요가 없다. 모든 경로는 이 독립 저장소의 루트 기준이다.

## 핵심 수학

- M=C(n+1,2), T_b=C(b,2), y=sM+T_b+a (0≤s<n, 0≤a<b≤n).
- 색 C(x,y)=s+[x if x<b; a if x=b; x−1 if x>b] mod n.
- 행에서 반복되는 유일한 열쌍은 (a,b), 색은 s+a mod n. 모든 색·열쌍이 정확히 한 번.
- 기울어진 직사각형 높이 H≤floor(n²/4)+1. 따라서 블록 두 개까지만 분석.
- 고정 색의 한 블록 기본번호 k: O는 열 k+1→k인 감소 계단, S는 (b,T_b+k), b≥k+1.
- 일반 경계 k→k−1: O의 전환 거리 M−k>H. S의 모든 기울기 절댓값≥1; 세 S가 직각인 유일한 등호 사례는 네 번째 꼭짓점 x=n+1로 범위 밖. 2O+2S는 중점 또는 높이 제한으로 배제.
- 순환 경계 0→n−1: 위 블록의 해당 범위 점은 열 n뿐. 최상단 꼭짓점이 최우측일 수 없어 배제.
- n=1,2는 작은 배열 직접 확인. 증명은 가로·세로 단위 간격이 같은 정사각 격자를 가정한다.


## 실행과 검증

```sh
lake update
lake exe cache get
lake build RectangleColoring
lake env lean lean/RectangleColoring/Main.lean
python verify.py --max-n 12
xelatex -interaction=nonstopmode -halt-on-error solution.tex
xelatex -interaction=nonstopmode -halt-on-error solution.tex
```

Lean과 Mathlib 버전은 `lean-toolchain`, `lakefile.toml`에 고정되어 있다. 17개 Lean 소스를 검사했고 최종 정리의 공리는 `propext`, `Classical.choice`, `Quot.sound`뿐이다. 프로젝트에 `sorry`, 추가 공리, `native_decide`가 없다. Python 결과를 Lean의 가정으로 사용하지 않는다. TeX는 XeLaTeX와 ko.TeX, 지정된 한글 글꼴 중 하나가 필요하다.

## 실패했던 접근과 주의

- 축평행 상한만으로 최소성을 주장하면 안 된다. 명시적 하한 구성의 모든 기울어진 경우를 배제했다.
- 작은 n의 검산은 일반 정리를 대신하지 않는다.
- 일반 `decide`의 큰 전개 대신 n=2 반례는 조건을 먼저 거른 `decide +kernel`로 검증했다.
- PDF의 본문과 수식, 페이지 나눔, 한글 글리프, 메타데이터를 확인했다. 컴파일 로그·임시 이미지는 저장소에 포함하지 않는다.

## 다음 작업

현재 정리의 증명에 남은 구멍은 없다. 내용 수정 시 관련 Lean 모듈을 검사하고 TeX/PDF를 함께 갱신한다. 수식이나 페이지 배치를 바꾸면 PDF를 렌더링해 검수한다. 이 인덱스와 `SUMMARY_FOR_ME.md`를 함께 갱신한다.
