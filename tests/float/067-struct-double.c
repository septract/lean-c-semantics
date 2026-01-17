// Test: double as struct member
struct Coord {
  double lat;
  double lon;
};

int main(void) {
  struct Coord c;
  c.lat = 37.7749;
  c.lon = -122.4194;
  return (c.lat == 37.7749 && c.lon == -122.4194) ? 0 : 1;
}
