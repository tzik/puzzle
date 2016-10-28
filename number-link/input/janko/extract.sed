/^problem$/,/^solution$/{
  s/^problem$//;t;
  s/^solution$//;t;
  s/-/0/g;
  p;
}
