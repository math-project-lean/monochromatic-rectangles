# 짧은 요약

- n색 격자점의 단색 직사각형 문제다. 기울어진 직사각형도 포함한 답은 **n²(n+1)/2+1**이다.
- `solution.pdf`로 풀이를 읽고, 수정하려면 `solution.tex`을 열어 XeLaTeX로 컴파일한다.
- `lean/RectangleColoring/Main.lean`에 일반 n의 최소값 정리가 있다. `lake build RectangleColoring`으로 검사한다.
- `python verify.py --max-n 12`로 유한 검산도 할 수 있다. 일반 증명은 이 계산과 독립적이다.
- 가로·세로 간격이 같은 정사각 격자를 전제로 한다. 개인 환경·임시 자료·빌드 결과는 공개 파일에 포함하지 않는다.
